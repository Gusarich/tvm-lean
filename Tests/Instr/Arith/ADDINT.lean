import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.ADDINT

/-
ADDINT branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/AddInt.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_add_tinyint8`, opcode wiring in `register_add_mul_ops`).

Branch counts used for this suite:
- Lean: 4 branch points / 6 terminal outcomes
  (opcode dispatch; `popInt` success vs underflow/type; finite-vs-NaN split;
   `pushIntQuiet` signed-257 fit check in non-quiet mode).
- C++: 3 branch points / 6 aligned terminal outcomes
  (`check_underflow`; `pop_int` type check; `push_int_quiet` success vs `int_ov`
   for NaN/overflow results).

Mapped terminal outcomes covered:
- success (finite result),
- `stkUnd`,
- `typeChk`,
- `intOv` from NaN propagation,
- `intOv` from positive overflow,
- `intOv` from negative underflow.

Key divergence risk areas:
- tinyint8 two's-complement decode boundaries (`-128`, `-1`, `0`, `127`);
- immediate encode range guard (`[-128, 127]`) and 16-bit decode consumption;
- non-quiet NaN path must throw `intOv` (not push NaN);
- signed-257 off-by-one behavior near `minInt257` / `maxInt257`;
- precise gas threshold for `PUSHINT n; SETGASLIMIT; ADDINT imm`.
-/

private def addIntId : InstrId := { name := "ADDINT" }

private def intV (n : Int) : Value :=
  .int (.num n)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := addIntId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkAddIntCase
    (name : String)
    (imm : Int)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[.addInt imm] gasLimits fuel

private def runAddIntDirect (imm : Int) (stack : Array Value) : Except Excno (Array Value) :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrArithAddInt (.addInt imm) (pure ())).run st0
  match res with
  | .ok _ => .ok st1.stack
  | .error e => .error e

private def runAddIntDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrArithAddInt .add (VM.push (intV 777))).run st0
  match res with
  | .ok _ => .ok st1.stack
  | .error e => .error e

private def expectOkStack
    (label : String)
    (res : Except Excno (Array Value))
    (expected : Array Value) : IO Unit := do
  match res with
  | .ok st =>
      if st == expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected stack {reprStr expected}, got {reprStr st}")
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")

private def expectErr
    (label : String)
    (res : Except Excno (Array Value))
    (expected : Excno) : IO Unit := do
  match res with
  | .ok st =>
      throw (IO.userError s!"{label}: expected error {expected}, got stack {reprStr st}")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")

private def expectAssembleErr
    (label : String)
    (program : List Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 program with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {e}")

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure s'

private def addIntGasForInstr (instr : Instr) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok budget => budget
  | .error _ => instrGas instr 16

private def addIntGasProbeImm : Int := 7

private def addIntSetGasNeed (n : Int) : Int :=
  addIntGasForInstr (.pushInt (.num n))
    + addIntGasForInstr (.tonEnvOp .setGasLimit)
    + addIntGasForInstr (.addInt addIntGasProbeImm)
    + implicitRetGasPrice

private def addIntSetGasFixedPoint (n : Int) : Nat → Int
  | 0 => n
  | k + 1 =>
      let n' := addIntSetGasNeed n
      if n' = n then n else addIntSetGasFixedPoint n' k

private def addIntSetGasExact : Int :=
  addIntSetGasFixedPoint 64 16

private def addIntSetGasExactMinusOne : Int :=
  if addIntSetGasExact > 0 then addIntSetGasExact - 1 else 0

private def tinyInt8BoundaryPool : Array Int :=
  #[-128, -127, -1, 0, 1, 126, 127]

private def pickTinyInt8Boundary (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (tinyInt8BoundaryPool.size - 1)
  (tinyInt8BoundaryPool[idx]!, rng')

private def pickTinyInt8Uniform (rng : StdGen) : Int × StdGen :=
  let (u, rng') := randNat rng 0 255
  let n : Int := if u < 128 then Int.ofNat u else Int.ofNat u - 256
  (n, rng')

private def pickTinyInt8Mixed (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then pickTinyInt8Boundary rng1 else pickTinyInt8Uniform rng1

private def genAddIntFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 5
  let ((x, imm), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (imm0, r3) := pickTinyInt8Boundary r2
      ((x0, imm0), r3)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (imm0, r3) := pickTinyInt8Boundary r2
      ((x0, imm0), r3)
    else if shape = 2 then
      let (x0, r2) := pickInt257Boundary rng1
      let (imm0, r3) := pickTinyInt8Mixed r2
      ((x0, imm0), r3)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (imm0, r3) := pickTinyInt8Mixed r2
      ((x0, imm0), r3)
    else if shape = 4 then
      let (useMax, r2) := randBool rng1
      let x0 := if useMax then maxInt257 else minInt257
      let (imm0, r3) := pickTinyInt8Boundary r2
      ((x0, imm0), r3)
    else
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
  let (tag, rng3) := randNat rng2 0 999_999
  (mkAddIntCase s!"fuzz/shape-{shape}-{tag}" imm #[intV x], rng3)

def suite : InstrSuite where
  id := addIntId
  unit := #[
    { name := "unit/direct/finite-sign-zero-and-immediate-boundaries"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (17, 25, 42),
            (17, -5, 12),
            (-17, 5, -12),
            (-17, -5, -22),
            (123, 0, 123),
            (5, -128, -123),
            (5, 127, 132),
            (maxInt257, -1, maxInt257 - 1),
            (minInt257, 1, minInt257 + 1)
          ]
        for c in checks do
          let x := c.1
          let imm := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}+{imm}" (runAddIntDirect imm #[intV x]) #[intV expected] }
    ,
    { name := "unit/immediate/decode-boundary-sequence"
      run := do
        let program : Array Instr :=
          #[.addInt (-128), .addInt (-1), .addInt 0, .addInt 1, .addInt 127, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/-128" s0 (.addInt (-128)) 16
        let s2 ← expectDecodeStep "decode/-1" s1 (.addInt (-1)) 16
        let s3 ← expectDecodeStep "decode/0" s2 (.addInt 0) 16
        let s4 ← expectDecodeStep "decode/1" s3 (.addInt 1) 16
        let s5 ← expectDecodeStep "decode/127" s4 (.addInt 127) 16
        let s6 ← expectDecodeStep "decode/tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/tail-add: expected exhausted slice, got {s6.bitsRemaining} bits remaining") }
    ,
    { name := "unit/immediate/assembler-range-check"
      run := do
        expectAssembleErr "addint/128" [.addInt 128] .rangeChk
        expectAssembleErr "addint/-129" [.addInt (-129)] .rangeChk }
    ,
    { name := "unit/error/intov-underflow-type-ordering"
      run := do
        expectErr "overflow/max+1" (runAddIntDirect 1 #[intV maxInt257]) .intOv
        expectErr "overflow/min-1" (runAddIntDirect (-1) #[intV minInt257]) .intOv
        expectErr "nan+1" (runAddIntDirect 1 #[.int .nan]) .intOv
        expectErr "empty-underflow" (runAddIntDirect 0 #[]) .stkUnd
        expectErr "nonint-typechk" (runAddIntDirect 0 #[.null]) .typeChk }
    ,
    { name := "unit/dispatch/non-addint-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runAddIntDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkAddIntCase "ok/zero/x-zero-imm-zero" 0 #[intV 0],
    mkAddIntCase "ok/sign/pos-plus-pos-imm" 25 #[intV 17],
    mkAddIntCase "ok/sign/pos-plus-neg-imm" (-5) #[intV 17],
    mkAddIntCase "ok/sign/neg-plus-pos-imm" 5 #[intV (-17)],
    mkAddIntCase "ok/sign/neg-plus-neg-imm" (-5) #[intV (-17)],
    mkAddIntCase "ok/zero/imm-zero-noop" 0 #[intV 123],
    mkAddIntCase "immediate/min-imm-neg128" (-128) #[intV 5],
    mkAddIntCase "immediate/max-imm-pos127" 127 #[intV 5],
    mkCase "immediate/decode-sequence-min-max" #[intV 1] #[.addInt (-128), .addInt 127],
    mkAddIntCase "boundary/max-plus-zero-imm" 0 #[intV maxInt257],
    mkAddIntCase "boundary/min-plus-zero-imm" 0 #[intV minInt257],
    mkAddIntCase "boundary/max-plus-neg-one" (-1) #[intV maxInt257],
    mkAddIntCase "boundary/min-plus-one" 1 #[intV minInt257],
    mkAddIntCase "boundary/near-max-plus-one-non-overflow" 1 #[intV (maxInt257 - 1)],
    mkAddIntCase "boundary/near-min-minus-one-non-overflow" (-1) #[intV (minInt257 + 1)],
    mkAddIntCase "overflow/max-plus-one" 1 #[intV maxInt257],
    mkAddIntCase "overflow/min-minus-one" (-1) #[intV minInt257],
    mkAddIntCase "overflow/max-plus-max-imm" 127 #[intV maxInt257],
    mkAddIntCase "overflow/min-plus-min-imm" (-128) #[intV minInt257],
    mkAddIntCase "underflow/empty-stack" 0 #[],
    mkAddIntCase "type/top-null" 0 #[.null],
    mkAddIntCase "type/top-cell" 0 #[.cell Cell.empty],
    mkAddIntCase "error-order/empty-underflow-before-type" 127 #[],
    mkAddIntCase "error-order/non-empty-type-check" (-128) #[.null],
    mkCase "nan/pushnan-propagates-intov" #[intV 42] #[.pushInt .nan, .addInt 1],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num addIntSetGasExact), .tonEnvOp .setGasLimit, .addInt addIntGasProbeImm],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num addIntSetGasExactMinusOne), .tonEnvOp .setGasLimit, .addInt addIntGasProbeImm]
  ]
  fuzz := #[
    { seed := 2026020802
      count := 500
      gen := genAddIntFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.ADDINT
