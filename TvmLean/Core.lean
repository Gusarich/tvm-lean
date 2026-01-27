import Std

namespace TvmLean

/-! A small, executable “Milestone 1” core:

- Core datatypes (`IntVal`, `Value`, `Continuation`, `VmState`)
- A tiny instruction AST and an executable `step`
- WF predicates + theorem statements (mostly `sorry` for now)

This is intentionally minimal and designed to be refactored as we add decoding/cells/dicts/opcodes.
-/

inductive Excno : Type
  | none
  | alt
  | stkUnd
  | stkOv
  | intOv
  | rangeChk
  | invOpcode
  | typeChk
  | cellOv
  | cellUnd
  | dictErr
  | unknown
  | fatal
  | outOfGas
  | virtErr
  deriving DecidableEq, Repr

def Excno.toInt : Excno → Int
  | .none => 0
  | .alt => 1
  | .stkUnd => 2
  | .stkOv => 3
  | .intOv => 4
  | .rangeChk => 5
  | .invOpcode => 6
  | .typeChk => 7
  | .cellOv => 8
  | .cellUnd => 9
  | .dictErr => 10
  | .unknown => 11
  | .fatal => 12
  | .outOfGas => 13
  | .virtErr => 14

inductive IntVal : Type
  | nan
  | num (n : Int)
  deriving DecidableEq, Repr

def IntVal.isValid : IntVal → Bool
  | .nan => false
  | .num _ => true

def IntVal.signedFits257 : IntVal → Bool
  | .nan => false
  | .num n =>
      -- [-2^256, 2^256)
      let lo : Int := -((2 : Int) ^ (256 : Nat))
      let hi : Int := (2 : Int) ^ (256 : Nat)
      decide (lo ≤ n ∧ n < hi)

def IntVal.add (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => .num (a + b)
  | _, _ => .nan

def IntVal.inc (x : IntVal) : IntVal :=
  x.add (.num 1)

def IntVal.equalResult (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => if a = b then .num (-1) else .num 0
  | _, _ => .nan

def IntVal.toBool? (x : IntVal) : Except Excno Bool :=
  match x with
  | .nan => .error .intOv
  | .num n => .ok (n ≠ 0)

abbrev BitString := Array Bool

def bitsToNat (bs : BitString) : Nat :=
  bs.foldl (fun acc b => (acc <<< 1) + (if b then 1 else 0)) 0

def natToBits (n bits : Nat) : BitString :=
  Array.ofFn (n := bits) fun i =>
    let k := bits - 1 - i.1
    n.testBit k

def intPow2 (bits : Nat) : Int :=
  (2 : Int) ^ bits

structure Cell where
  bits : BitString
  refs : Array Cell
  deriving Repr

def Cell.empty : Cell :=
  { bits := #[], refs := #[] }

def Cell.ofUInt (bits : Nat) (n : Nat) : Cell :=
  { bits := natToBits n bits, refs := #[] }

structure Slice where
  cell : Cell
  bitPos : Nat
  refPos : Nat
  deriving Repr

def Slice.ofCell (c : Cell) : Slice :=
  { cell := c, bitPos := 0, refPos := 0 }

def Slice.bitsRemaining (s : Slice) : Nat :=
  s.cell.bits.size - s.bitPos

def Slice.refsRemaining (s : Slice) : Nat :=
  s.cell.refs.size - s.refPos

def Slice.haveBits (s : Slice) (n : Nat) : Bool :=
  decide (s.bitPos + n ≤ s.cell.bits.size)

def Slice.readBits (s : Slice) (n : Nat) : BitString :=
  s.cell.bits.extract s.bitPos (s.bitPos + n)

def Slice.advanceBits (s : Slice) (n : Nat) : Slice :=
  { s with bitPos := s.bitPos + n }

structure Builder where
  bits : BitString
  refs : Array Cell
  deriving Repr

def Builder.empty : Builder :=
  { bits := #[], refs := #[] }

def Builder.canExtendBy (b : Builder) (bits : Nat) (refs : Nat := 0) : Bool :=
  decide (b.bits.size + bits ≤ 1023 ∧ b.refs.size + refs ≤ 4)

def Builder.storeBits (b : Builder) (bs : BitString) : Builder :=
  { b with bits := b.bits ++ bs }

def Builder.finalize (b : Builder) : Cell :=
  { bits := b.bits, refs := b.refs }

inductive Instr : Type
  | nop
  | pushInt (n : IntVal)
  | push (idx : Nat)    -- PUSH s[idx]
  | pop (idx : Nat)     -- POP s[idx]
  | xchg0 (idx : Nat)   -- XCHG s0,s[idx]
  | pushCtr (idx : Nat) -- PUSHCTRX <idx> (we'll use it for c4/c5/c7 too)
  | popCtr (idx : Nat)  -- POPCTRX <idx>
  | ctos
  | newc
  | endc
  | ends
  | ldu (bits : Nat)
  | stu (bits : Nat)
  | inc
  | equal
  | throwIfNot (exc : Int) -- THROWIFNOT <exc>
  deriving DecidableEq, Repr

inductive Continuation : Type
  | ordinary (code : List Instr)
  | quit (exitCode : Int)
  | excQuit
  deriving DecidableEq, Repr

inductive Value : Type
  | int (i : IntVal)
  | cell (c : Cell)
  | slice (s : Slice)
  | builder (b : Builder)
  | tuple (t : Array Value)
  | cont (k : Continuation)
  | null
  deriving Repr

instance : Inhabited Value := ⟨.null⟩

def Value.pretty : Value → String
  | .int .nan => "NaN"
  | .int (.num n) => toString n
  | .null => "null"
  | .cell _ => "<cell>"
  | .slice _ => "<slice>"
  | .builder _ => "<builder>"
  | .tuple t => s!"<tuple:{t.size}>"
  | .cont k =>
      match k with
      | .ordinary _ => "<cont:ord>"
      | .quit n => s!"<cont:quit {n}>"
      | .excQuit => "<cont:excquit>"

instance : ToString Value := ⟨Value.pretty⟩

abbrev Stack := Array Value

structure GasLimits where
  gasMax : Int
  gasLimit : Int
  gasCredit : Int
  gasRemaining : Int
  gasBase : Int
  deriving Repr

def GasLimits.infty : Int := (Int.ofNat (1 <<< 63)) - 1

def GasLimits.default : GasLimits :=
  { gasMax := GasLimits.infty
    gasLimit := GasLimits.infty
    gasCredit := 0
    gasRemaining := GasLimits.infty
    gasBase := GasLimits.infty }

structure Regs where
  c0 : Continuation
  c1 : Continuation
  c2 : Continuation
  c3 : Continuation
  c4 : Cell
  c5 : Cell
  c7 : Array Value
  deriving Repr

def Regs.initial : Regs :=
  { c0 := .quit 0
    c1 := .quit 1
    c2 := .excQuit
    c3 := .quit 11
    c4 := Cell.empty
    c5 := Cell.empty
    c7 := #[] }

structure VmState where
  stack : Stack
  regs : Regs
  cc : Continuation
  cp : Int
  gas : GasLimits
  deriving Repr

def VmState.initial (code : List Instr) : VmState :=
  { stack := #[]
    regs := Regs.initial
    cc := .ordinary code
    cp := 0
    gas := GasLimits.default }

abbrev VM := ExceptT Excno (StateM VmState)

def VM.push (v : Value) : VM Unit := do
  modify fun st => { st with stack := st.stack.push v }

def VM.pop : VM Value := do
  let st ← get
  if h : 0 < st.stack.size then
    let v := st.stack.back (h := h)
    modify fun st => { st with stack := st.stack.pop }
    return v
  else
    throw .stkUnd

def VM.fetch (idxFromTop : Nat) : VM Value := do
  let st ← get
  if _h : idxFromTop < st.stack.size then
    let pos := st.stack.size - 1 - idxFromTop
    return st.stack[pos]!
  else
    throw .stkUnd

def VM.swap (iFromTop jFromTop : Nat) : VM Unit := do
  let st ← get
  let need := Nat.max iFromTop jFromTop
  if _h : need < st.stack.size then
    let pi := st.stack.size - 1 - iFromTop
    let pj := st.stack.size - 1 - jFromTop
    let vi := st.stack[pi]!
    let vj := st.stack[pj]!
    modify fun st =>
      let s := st.stack
      { st with stack := (s.set! pi vj).set! pj vi }
  else
    throw .stkUnd

def VM.popInt : VM IntVal := do
  let v ← VM.pop
  match v with
  | .int i => return i
  | _ => throw .typeChk

def VM.popCell : VM Cell := do
  let v ← VM.pop
  match v with
  | .cell c => return c
  | _ => throw .typeChk

def VM.popSlice : VM Slice := do
  let v ← VM.pop
  match v with
  | .slice s => return s
  | _ => throw .typeChk

def VM.popBuilder : VM Builder := do
  let v ← VM.pop
  match v with
  | .builder b => return b
  | _ => throw .typeChk

def VM.popBool : VM Bool := do
  let i ← VM.popInt
  match i.toBool? with
  | .ok b => return b
  | .error e => throw e

def VM.pushIntQuiet (i : IntVal) (quiet : Bool) : VM Unit := do
  if i.signedFits257 then
    VM.push (.int i)
  else
    if quiet then
      VM.push (.int .nan)
    else
      throw .intOv

def VM.pushSmallInt (n : Int) : VM Unit := do
  -- Always fits 257-bit in practice for our uses.
  VM.push (.int (.num n))

def VmState.throwException (st : VmState) (exc : Int) : VmState :=
  let stack : Stack := #[.int (.num 0), .int (.num exc)]
  { st with
    stack := stack
    cc := st.regs.c2 }

def VmState.getCtr (st : VmState) (idx : Nat) : Except Excno Value :=
  match idx with
  | 0 => .ok (.cont st.regs.c0)
  | 1 => .ok (.cont st.regs.c1)
  | 2 => .ok (.cont st.regs.c2)
  | 3 => .ok (.cont st.regs.c3)
  | 4 => .ok (.cell st.regs.c4)
  | 5 => .ok (.cell st.regs.c5)
  | 7 => .ok (.tuple st.regs.c7)
  | _ => .error .rangeChk

def VmState.setCtr (st : VmState) (idx : Nat) (v : Value) : Except Excno VmState :=
  match idx, v with
  | 0, .cont k => .ok { st with regs := { st.regs with c0 := k } }
  | 1, .cont k => .ok { st with regs := { st.regs with c1 := k } }
  | 2, .cont k => .ok { st with regs := { st.regs with c2 := k } }
  | 3, .cont k => .ok { st with regs := { st.regs with c3 := k } }
  | 4, .cell c => .ok { st with regs := { st.regs with c4 := c } }
  | 5, .cell c => .ok { st with regs := { st.regs with c5 := c } }
  | 7, .tuple t => .ok { st with regs := { st.regs with c7 := t } }
  | 6, _ => .error .rangeChk
  | _, _ => .error .typeChk

def execInstr (i : Instr) : VM Unit := do
  match i with
  | .nop =>
      pure ()
  | .pushInt n =>
      VM.pushIntQuiet n false
  | .push idx =>
      let v ← VM.fetch idx
      VM.push v
  | .pop idx =>
      -- Mirror the C++ behavior: swap top with s[idx], then pop the top.
      VM.swap 0 idx
      let _ ← VM.pop
      pure ()
  | .xchg0 idx =>
      VM.swap 0 idx
  | .pushCtr idx =>
      let st ← get
      match st.getCtr idx with
      | .ok v => VM.push v
      | .error e => throw e
  | .popCtr idx =>
      let v ← VM.pop
      let st ← get
      match st.setCtr idx v with
      | .ok st' => set st'
      | .error e => throw e
  | .ctos =>
      let c ← VM.popCell
      VM.push (.slice (Slice.ofCell c))
  | .newc =>
      VM.push (.builder Builder.empty)
  | .endc =>
      let b ← VM.popBuilder
      VM.push (.cell b.finalize)
  | .ends =>
      let s ← VM.popSlice
      if s.bitsRemaining == 0 && s.refsRemaining == 0 then
        pure ()
      else
        throw .cellUnd
  | .ldu bits =>
      if bits == 0 then
        throw .rangeChk
      let s ← VM.popSlice
      if s.haveBits bits then
        let bs := s.readBits bits
        let n := bitsToNat bs
        VM.push (.int (.num (Int.ofNat n)))
        VM.push (.slice (s.advanceBits bits))
      else
        throw .cellUnd
  | .stu bits =>
      if bits == 0 then
        throw .rangeChk
      -- Match C++ operand order for `STU`: builder is on top, integer is below.
      let b ← VM.popBuilder
      let x ← VM.popInt
      if !b.canExtendBy bits then
        throw .cellOv
      match x with
      | .nan => throw .rangeChk
      | .num n =>
          if decide (n < 0 ∨ n ≥ intPow2 bits) then
            throw .rangeChk
          let bs := natToBits n.toNat bits
          VM.push (.builder (b.storeBits bs))
  | .inc =>
      let x ← VM.popInt
      VM.pushIntQuiet (x.inc) false
  | .equal =>
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.equalResult y) false
  | .throwIfNot exc =>
      let flag ← VM.popBool
      if flag then
        pure ()
      else
        modify fun st => st.throwException exc

inductive StepResult : Type
  | continue (st : VmState)
  | halt (exitCode : Int) (st : VmState)
  deriving Repr

def VmState.step (st : VmState) : StepResult :=
  match st.cc with
  | .quit n =>
      .halt (~~~ n) st
  | .excQuit =>
      let action : VM Int := do
        -- Match `pop_smallint_range(0xffff)` behavior closely enough for MVP.
        let v ← VM.popInt
        match v with
        | .nan => throw .rangeChk
        | .num n =>
            if n < 0 ∨ n > 0xffff then
              throw .rangeChk
            else
              return n
      let (res, st') := (action.run st)
      let n : Int :=
        match res with
        | .ok n => n
        | .error e => e.toInt
      .halt (~~~ n) st'
  | .ordinary code =>
      match code with
      | [] =>
          -- MVP model: implicit RET jumps to c0.
          .continue { st with cc := st.regs.c0 }
      | instr :: rest =>
          let st0 := { st with cc := .ordinary rest }
          let (res, st1) := (execInstr instr).run st0
          match res with
          | .ok _ => .continue st1
          | .error e =>
              -- Unhandled VM error: “throw exception code and jump to c2”.
              .continue (st1.throwException e.toInt)

def VmState.tryCommit (_st : VmState) : Bool :=
  -- Milestone 1: keep the hook (C++ has depth/level checks); always succeed for now.
  true

def VmState.run (fuel : Nat) (st : VmState) : StepResult :=
  match fuel with
  | 0 => .halt (Excno.fatal.toInt) st
  | fuel + 1 =>
      match st.step with
      | .continue st' => VmState.run fuel st'
      | .halt exitCode st' =>
          -- Mirror the C++ commit wrapper shape; precise commit checks come later.
          if exitCode = -1 ∨ exitCode = -2 then
            if st'.tryCommit then
              .halt exitCode st'
            else
              -- C++: clear stack, push 0, return ~cell_ov on commit failure.
              let st'' := { st' with stack := #[.int (.num 0)] }
              .halt (~~~ Excno.cellOv.toInt) st''
          else
            .halt exitCode st'

def Stack.pretty (s : Stack) : String :=
  let elems := s.toList.map (fun v => v.pretty)
  "[" ++ String.intercalate ", " elems ++ "]"

/-! ### Proof scaffolding (Milestone 1, mostly `sorry`) -/

def WF_Int : IntVal → Prop
  | .nan => True
  | .num n =>
      let lo : Int := -((2 : Int) ^ (256 : Nat))
      let hi : Int := (2 : Int) ^ (256 : Nat)
      lo ≤ n ∧ n < hi

def WF_Cell (_c : Cell) : Prop := True
def WF_Slice (_s : Slice) : Prop := True
def WF_Builder (_b : Builder) : Prop := True

def WF_Value : Value → Prop
  | .int i => WF_Int i
  | .cell c => WF_Cell c
  | .slice s => WF_Slice s
  | .builder b => WF_Builder b
  | .tuple _ => True
  | .cont _ => True
  | .null => True

def WF_Regs (_r : Regs) : Prop := True

def WF_State (st : VmState) : Prop :=
  (∀ v ∈ st.stack.toList, WF_Value v) ∧ WF_Regs st.regs

theorem step_preserves_wf {st : VmState} :
    WF_State st →
      match st.step with
      | .continue st' => WF_State st'
      | .halt _ st' => WF_State st' := by
  sorry

theorem run_preserves_wf {fuel : Nat} {st : VmState} :
    WF_State st →
      match VmState.run fuel st with
      | .continue st' => WF_State st'
      | .halt _ st' => WF_State st' := by
  sorry

end TvmLean
