import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.GTINT

/-
GTINT branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/GtInt.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_cmp_int`, opcode wiring in `register_int_cmp_ops`).

Branch counts used for this suite:
- Lean: 4 branch points / 6 terminal outcomes
  (opcode dispatch; `popInt` success vs underflow/type; finite-vs-NaN split;
   strict-greater predicate for finite integers).
- C++: 4 branch points / 6 aligned terminal outcomes
  (`check_underflow`; `pop_int` type check; valid-vs-NaN split via `is_valid`;
   comparison result mapped by GT mode to `-1` for greater and `0` otherwise).

Mapped terminal outcomes covered:
- success (`-1` when `x > imm`, `0` when `x ≤ imm`),
- `stkUnd`,
- `typeChk`,
- `intOv` from NaN propagation in non-quiet mode.

Key divergence risk areas:
- tinyint8 two's-complement immediate decode boundaries (`-128`, `-1`, `0`, `127`);
- immediate encode range guard (`[-128, 127]`) and 16-bit decode consumption;
- NaN path in non-quiet mode must throw `intOv`;
- strict-greater truth mapping (`x = imm` must yield `0`, not `-1`);
- precise gas threshold for `PUSHINT n; SETGASLIMIT; GTINT imm`.
-/

private def gtIntId : InstrId := { name := "GTINT" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := gtIntId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkGtIntCase
    (name : String)
    (imm : Int)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[.gtInt imm] gasLimits fuel

private def runGtIntDirect (imm : Int) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithGtInt (.gtInt imm) stack

private def runGtIntDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithGtInt .add (VM.push (intV 777)) stack

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

private def gtIntGasProbeImm : Int := 7

private def gtIntSetGasExact : Int :=
  computeExactGasBudget (.gtInt gtIntGasProbeImm)

private def gtIntSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.gtInt gtIntGasProbeImm)

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

private def genGtIntFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
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
  (mkGtIntCase s!"fuzz/shape-{shape}-{tag}" imm #[intV x], rng3)

def suite : InstrSuite where
  id := gtIntId
  unit := #[
    { name := "unit/direct/finite-greater-results-and-immediate-boundaries"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (17, 17, 0),
            (25, 17, -1),
            (17, 25, 0),
            (-17, -17, 0),
            (-5, -17, -1),
            (-17, 5, 0),
            (5, -128, -1),
            (5, 127, 0),
            (-128, -128, 0),
            (127, 127, 0),
            (maxInt257, 127, -1),
            (minInt257, -128, 0)
          ]
        for c in checks do
          let x := c.1
          let imm := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}>{imm}" (runGtIntDirect imm #[intV x]) #[intV expected] }
    ,
    { name := "unit/immediate/decode-boundary-sequence"
      run := do
        let program : Array Instr :=
          #[.gtInt (-128), .gtInt (-1), .gtInt 0, .gtInt 1, .gtInt 127, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/-128" s0 (.gtInt (-128)) 16
        let s2 ← expectDecodeStep "decode/-1" s1 (.gtInt (-1)) 16
        let s3 ← expectDecodeStep "decode/0" s2 (.gtInt 0) 16
        let s4 ← expectDecodeStep "decode/1" s3 (.gtInt 1) 16
        let s5 ← expectDecodeStep "decode/127" s4 (.gtInt 127) 16
        let s6 ← expectDecodeStep "decode/tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/tail-add: expected exhausted slice, got {s6.bitsRemaining} bits remaining") }
    ,
    { name := "unit/immediate/assembler-range-check"
      run := do
        expectAssembleErr "gtint/128" [.gtInt 128] .rangeChk
        expectAssembleErr "gtint/-129" [.gtInt (-129)] .rangeChk }
    ,
    { name := "unit/error/intov-underflow-type-ordering"
      run := do
        expectErr "nan/gtint" (runGtIntDirect 1 #[.int .nan]) .intOv
        expectErr "empty-underflow" (runGtIntDirect 0 #[]) .stkUnd
        expectErr "nonint-typechk" (runGtIntDirect 0 #[.null]) .typeChk
        expectErr "error-order/underflow-before-type" (runGtIntDirect 127 #[]) .stkUnd
        expectErr "error-order/type-when-non-empty" (runGtIntDirect (-128) #[.cell Cell.empty]) .typeChk }
    ,
    { name := "unit/dispatch/non-gtint-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runGtIntDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkGtIntCase "ok/not-greater/equal-zero" 0 #[intV 0],
    mkGtIntCase "ok/greater/positive" 17 #[intV 25],
    mkGtIntCase "ok/not-greater/positive" 25 #[intV 17],
    mkGtIntCase "ok/greater/negative" (-17) #[intV (-5)],
    mkGtIntCase "ok/not-greater/negative" (-5) #[intV (-17)],
    mkGtIntCase "immediate/min-neg128-x-greater" (-128) #[intV (-127)],
    mkGtIntCase "immediate/min-neg128-x-equal" (-128) #[intV (-128)],
    mkGtIntCase "immediate/max-pos127-x-greater" 127 #[intV maxInt257],
    mkGtIntCase "immediate/max-pos127-x-not-greater" 127 #[intV 127],
    mkGtIntCase "boundary/max-int-greater-than-min-imm" (-128) #[intV maxInt257],
    mkGtIntCase "boundary/min-int-not-greater-than-max-imm" 127 #[intV minInt257],
    mkGtIntCase "boundary/near-max-greater-than-126" 126 #[intV (maxInt257 - 1)],
    mkGtIntCase "boundary/near-min-not-greater-than-neg127" (-127) #[intV (minInt257 + 1)],
    mkGtIntCase "underflow/empty-stack" 0 #[],
    mkGtIntCase "type/top-null" 0 #[.null],
    mkGtIntCase "type/top-cell" 0 #[.cell Cell.empty],
    mkGtIntCase "error-order/empty-underflow-before-type" 127 #[],
    mkGtIntCase "error-order/non-empty-type-check" (-128) #[.null],
    mkCase "nan/pushnan-propagates-intov" #[intV 42] #[.pushInt .nan, .gtInt 1],
    mkCase "gas/exact-cost-succeeds" #[intV gtIntGasProbeImm]
      #[.pushInt (.num gtIntSetGasExact), .tonEnvOp .setGasLimit, .gtInt gtIntGasProbeImm],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV gtIntGasProbeImm]
      #[.pushInt (.num gtIntSetGasExactMinusOne), .tonEnvOp .setGasLimit, .gtInt gtIntGasProbeImm]
  ]
  fuzz := #[
    { seed := 2026020810
      count := 500
      gen := genGtIntFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.GTINT
