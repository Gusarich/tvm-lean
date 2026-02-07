import TvmLean.Model
import TvmLean.Semantics.VM.Monad
import TvmLean.Semantics.VM.Ops.Stack
import TvmLean.Semantics.VM.Ops.Gas

namespace TvmLean

def VmState.throwException (st : VmState) (exc : Int) : VmState :=
  let stack : Stack := #[.int (.num 0), .int (.num exc)]
  { st with
    stack := stack
    cc := st.regs.c2 }

def VmState.throwExceptionArg (st : VmState) (exc : Int) (arg : Value) : VmState :=
  let stack : Stack := #[arg, .int (.num exc)]
  { st with
    stack := stack
    cc := st.regs.c2 }

def VmState.ret (st : VmState) : VmState :=
  -- Mirrors C++ `VmState::ret()` as a jump to old `c0` after swapping `c0 := quit0`.
  let cont := st.regs.c0
  { st with regs := { st.regs with c0 := .quit 0 }, cc := cont }

def VmState.retAlt (st : VmState) : VmState :=
  -- Mirrors C++ `VmState::ret_alt()` as a jump to old `c1` after swapping `c1 := quit1`.
  let cont := st.regs.c1
  { st with regs := { st.regs with c1 := .quit 1 }, cc := cont }

def VmState.jumpTo (st : VmState) (k : Continuation) : VmState :=
  { st with cc := k }

def VmState.callToWithFrame (st : VmState) (frame : CallFrame) (k : Continuation) : VmState :=
  let oldC0 := st.regs.c0
  let retCont :=
    match st.cc with
    | .ordinary code _ _ _ =>
        -- Store the "old c0" in the return continuation's saved cregs, matching C++ `ControlData.save.c0`.
        let cregsRet : OrdCregs := { OrdCregs.empty with c0 := some oldC0 }
        let cdataRet : OrdCdata := { stack := frame.savedStack, nargs := frame.retArgs }
        .ordinary code (.quit 0) cregsRet cdataRet
    | _ => .quit 0
  { st with regs := { st.regs with c0 := retCont }, cc := k }

def VmState.callTo (st : VmState) (k : Continuation) : VmState :=
  st.callToWithFrame CallFrame.identity k

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
  match idx with
  | 0 =>
      match v with
      | .cont k => .ok { st with regs := { st.regs with c0 := k } }
      | _ => .error .typeChk
  | 1 =>
      match v with
      | .cont k => .ok { st with regs := { st.regs with c1 := k } }
      | _ => .error .typeChk
  | 2 =>
      match v with
      | .cont k => .ok { st with regs := { st.regs with c2 := k } }
      | _ => .error .typeChk
  | 3 =>
      match v with
      | .cont k => .ok { st with regs := { st.regs with c3 := k } }
      | _ => .error .typeChk
  | 4 =>
      match v with
      | .cell c => .ok { st with regs := { st.regs with c4 := c } }
      | _ => .error .typeChk
  | 5 =>
      match v with
      | .cell c => .ok { st with regs := { st.regs with c5 := c } }
      | _ => .error .typeChk
  | 7 =>
      match v with
      | .tuple t => .ok { st with regs := { st.regs with c7 := t } }
      | _ => .error .typeChk
  | _ =>
      .error .rangeChk

def tupleExtendSetIndex (t : Array Value) (idx : Nat) (v : Value) : Array Value × Nat :=
  if idx < t.size then
    (t.set! idx v, t.size)
  else if v == .null then
    (t, 0)
  else
    let newSize := idx + 1
    let tExt := t ++ Array.replicate (newSize - t.size) Value.null
    (tExt.set! idx v, newSize)

def VM.generateRandu256 : VM Int := do
  -- Mirrors `generate_randu256` from `crypto/vm/tonops.cpp`:
  -- SHA512(seed) where seed is a 256-bit unsigned integer, then:
  --   new_seed := hash[0:32], rand := hash[32:64].
  let st ← get
  match st.regs.c7[0]? with
  | none =>
      throw .rangeChk
  | some (Value.tuple params) =>
      match params[6]? with
      | none =>
          throw .rangeChk
      | some (Value.int (.num seed)) =>
          if decide (seed < 0 ∨ seed ≥ intPow2 256) then
            throw .rangeChk
          let seedBytes := natToBytesBEFixed seed.toNat 32
          let digest := sha512Digest seedBytes
          let newSeedNat := bytesToNatBE (digest.extract 0 32)
          let randNat := bytesToNatBE (digest.extract 32 64)
          let newSeed : Int := Int.ofNat newSeedNat
          let rand : Int := Int.ofNat randNat

          let (params', tpay) := tupleExtendSetIndex params 6 (Value.int (.num newSeed))
          let outerSize := st.regs.c7.size
          let c7' := st.regs.c7.set! 0 (Value.tuple params')
          let mut st' := { st with regs := { st.regs with c7 := c7' } }
          if tpay > 0 then
            st' := st'.consumeTupleGas tpay
          st' := st'.consumeTupleGas outerSize
          set st'
          return rand
      | some (Value.int .nan) =>
          throw .rangeChk
      | some _ =>
          throw .typeChk
  | some _ =>
      throw .typeChk

end TvmLean
