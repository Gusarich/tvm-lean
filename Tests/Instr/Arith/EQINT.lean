import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.EQINT

/-
EQINT branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/EqInt.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_cmp_int`, opcode wiring in `register_int_cmp_ops`).

Branch counts used for this suite:
- Lean: 4 branch points / 6 terminal outcomes
  (opcode dispatch; `popInt` success vs underflow/type; finite-vs-NaN split;
   equality predicate for finite integers).
- C++: 4 branch points / 6 aligned terminal outcomes
  (`check_underflow`; `pop_int` type check; valid-vs-NaN split via `is_valid`;
   comparison result mapped by EQ mode to `-1` for equal and `0` otherwise).

Mapped terminal outcomes covered:
- success (`-1` when equal, `0` when not equal),
- `stkUnd`,
- `typeChk`,
- `intOv` from NaN propagation in non-quiet mode.

Key divergence risk areas:
- tinyint8 two's-complement immediate decode boundaries (`-128`, `-1`, `0`, `127`);
- immediate encode range guard (`[-128, 127]`) and 16-bit decode consumption;
- NaN path in non-quiet mode must throw `intOv`;
- equality truth-value mapping must be TVM-boolean (`-1`) not `1`;
- precise gas threshold for `PUSHINT n; SETGASLIMIT; EQINT imm`.
-/

private def eqIntId : InstrId := { name := "EQINT" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := eqIntId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkEqIntCase
    (name : String)
    (imm : Int)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[.eqInt imm] gasLimits fuel

private def runEqIntDirect (imm : Int) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithEqInt (.eqInt imm) stack

private def runEqIntDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithEqInt .add (VM.push (intV 777)) stack

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

private def eqIntGasProbeImm : Int := 7

private def eqIntSetGasExact : Int :=
  computeExactGasBudget (.eqInt eqIntGasProbeImm)

private def eqIntSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.eqInt eqIntGasProbeImm)

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

private def genEqIntFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
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
      let (imm0, r2) := pickTinyInt8Mixed rng1
      ((imm0, imm0), r2)
    else if shape = 5 then
      let (imm0, r2) := pickTinyInt8Boundary rng1
      let (deltaIdx, r3) := randNat r2 0 3
      let delta : Int :=
        if deltaIdx = 0 then -2 else if deltaIdx = 1 then -1 else if deltaIdx = 2 then 1 else 2
      ((imm0 + delta, imm0), r3)
    else if shape = 6 then
      let (useMax, r2) := randBool rng1
      let x0 := if useMax then maxInt257 else minInt257
      let (imm0, r3) := pickTinyInt8Boundary r2
      ((x0, imm0), r3)
    else
      let (x0, r2) := pickSigned257ish rng1
      ((x0, 0), r2)
  let (tag, rng3) := randNat rng2 0 999_999
  (mkEqIntCase s!"fuzz/shape-{shape}-{tag}" imm #[intV x], rng3)

def suite : InstrSuite where
  id := eqIntId
  unit := #[
    { name := "unit/direct/finite-eq-results-and-immediate-boundaries"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, -1),
            (17, 17, -1),
            (17, 25, 0),
            (-17, -17, -1),
            (-17, 5, 0),
            (-128, -128, -1),
            (127, 127, -1),
            (5, -128, 0),
            (5, 127, 0),
            (maxInt257, 127, 0),
            (minInt257, -128, 0)
          ]
        for c in checks do
          let x := c.1
          let imm := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}=={imm}" (runEqIntDirect imm #[intV x]) #[intV expected] }
    ,
    { name := "unit/immediate/decode-boundary-sequence"
      run := do
        let program : Array Instr :=
          #[.eqInt (-128), .eqInt (-1), .eqInt 0, .eqInt 1, .eqInt 127, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/-128" s0 (.eqInt (-128)) 16
        let s2 ← expectDecodeStep "decode/-1" s1 (.eqInt (-1)) 16
        let s3 ← expectDecodeStep "decode/0" s2 (.eqInt 0) 16
        let s4 ← expectDecodeStep "decode/1" s3 (.eqInt 1) 16
        let s5 ← expectDecodeStep "decode/127" s4 (.eqInt 127) 16
        let s6 ← expectDecodeStep "decode/tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/tail-add: expected exhausted slice, got {s6.bitsRemaining} bits remaining") }
    ,
    { name := "unit/immediate/assembler-range-check"
      run := do
        expectAssembleErr "eqint/128" [.eqInt 128] .rangeChk
        expectAssembleErr "eqint/-129" [.eqInt (-129)] .rangeChk }
    ,
    { name := "unit/error/intov-underflow-type-ordering"
      run := do
        expectErr "nan/eqint" (runEqIntDirect 1 #[.int .nan]) .intOv
        expectErr "empty-underflow" (runEqIntDirect 0 #[]) .stkUnd
        expectErr "nonint-typechk" (runEqIntDirect 0 #[.null]) .typeChk
        expectErr "error-order/underflow-before-type" (runEqIntDirect 127 #[]) .stkUnd
        expectErr "error-order/type-when-non-empty" (runEqIntDirect (-128) #[.cell Cell.empty]) .typeChk }
    ,
    { name := "unit/dispatch/non-eqint-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runEqIntDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkEqIntCase "ok/equal/zero" 0 #[intV 0],
    mkEqIntCase "ok/equal/positive" 17 #[intV 17],
    mkEqIntCase "ok/equal/negative" (-17) #[intV (-17)],
    mkEqIntCase "ok/not-equal/positive" 25 #[intV 17],
    mkEqIntCase "ok/not-equal/negative" (-25) #[intV (-17)],
    mkEqIntCase "immediate/min-neg128-match" (-128) #[intV (-128)],
    mkEqIntCase "immediate/max-pos127-match" 127 #[intV 127],
    mkEqIntCase "immediate/min-neg128-mismatch" (-128) #[intV 127],
    mkEqIntCase "immediate/max-pos127-mismatch" 127 #[intV (-128)],
    mkEqIntCase "boundary/max-int-never-eq-tiny" 127 #[intV maxInt257],
    mkEqIntCase "boundary/min-int-never-eq-tiny" (-128) #[intV minInt257],
    mkEqIntCase "boundary/near-max-mismatch" 126 #[intV (maxInt257 - 1)],
    mkEqIntCase "boundary/near-min-mismatch" (-127) #[intV (minInt257 + 1)],
    mkEqIntCase "underflow/empty-stack" 0 #[],
    mkEqIntCase "type/top-null" 0 #[.null],
    mkEqIntCase "type/top-cell" 0 #[.cell Cell.empty],
    mkEqIntCase "error-order/empty-underflow-before-type" 127 #[],
    mkEqIntCase "error-order/non-empty-type-check" (-128) #[.null],
    mkCase "nan/pushnan-propagates-intov" #[intV 42] #[.pushInt .nan, .eqInt 1],
    mkCase "gas/exact-cost-succeeds" #[intV eqIntGasProbeImm]
      #[.pushInt (.num eqIntSetGasExact), .tonEnvOp .setGasLimit, .eqInt eqIntGasProbeImm],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV eqIntGasProbeImm]
      #[.pushInt (.num eqIntSetGasExactMinusOne), .tonEnvOp .setGasLimit, .eqInt eqIntGasProbeImm]
  ]
  fuzz := #[
    { seed := 2026020804
      count := 500
      gen := genEqIntFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.EQINT
