import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFT_HASH_MOD

/-
RSHIFT#MOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false false 3 (-1) false (some z)` specialization)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type/overflow behavior)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, `modPow2Round`, floor quotient/remainder invariants)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (hash-immediate encode gate for `z ∈ [1, 256]`, opcode family `0xa93c..0xa93e`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (hash-immediate decode family `0xa93c..0xa93e`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, non-quiet `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::rshift_any`, `AnyIntView::mod_pow2_any`)

Branch/terminal counts used for this suite (`mul=false`, `add=false`, `d=3`,
`roundMode=-1`, `quiet=false`, `zOpt=some z`):
- Lean specialization: ~6 branch sites / ~8 terminal outcomes
  (dispatch/fallback; underflow gate; single-operand pop/type split; fixed
   round-mode validity; numeric-vs-NaN path; two-result push with non-quiet
   overflow funnel).
- C++ specialization: ~6 branch sites / ~7 aligned terminal outcomes
  (`check_underflow(1)`; `pop_int` type split; floor q/r path; invalid-int
   funnel; non-quiet push overflow handling).

Key risk areas covered:
- hash-immediate discipline: shift is encoded and must not be popped from stack;
- floor quotient/remainder sign invariants across positive/negative and
  near-boundary operands (`±1`, `±2`, `±17`);
- boundary shifts (`1`, `255`, `256`) with signed-257 extremes;
- strict error ordering: underflow/type in direct handler, and `PUSHINT`
  overflow before instruction-level checks;
- NaN and out-of-range injection only via program prelude (never oracle/fuzz `initStack`);
- exact gas cliff (`SETGASLIMIT` exact vs exact-minus-one) via shared gas helpers.
-/

private def rshiftHashModId : InstrId := { name := "RSHIFT#MOD" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkRshiftHashModInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod false false 3 (-1) false (some shift))

private def rshiftHashModInstrDefault : Instr :=
  mkRshiftHashModInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[rshiftHashModInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := rshiftHashModId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkShiftCase
    (name : String)
    (shift : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[mkRshiftHashModInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (x : IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkRshiftHashModInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name stack (progPrefix.push instr) gasLimits fuel

private def runRshiftHashModDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkRshiftHashModInstr shift) stack

private def runRshiftHashModDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 7229)) stack

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

private def expectAssembleErr (label : String) (instr : Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {e}")

private def rshiftHashModGasProbeInstr : Instr :=
  mkRshiftHashModInstr 7

private def rshiftHashModSetGasExact : Int :=
  computeExactGasBudget rshiftHashModGasProbeInstr

private def rshiftHashModSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftHashModGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def nearBoundaryXPool : Array Int :=
  #[-17, -9, -3, -2, -1, 0, 1, 2, 3, 9, 17]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    pickShiftInRange rng1

private def pickNearBoundaryX (rng : StdGen) : Int × StdGen :=
  pickFromPool nearBoundaryXPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (useCell, rng') := randBool rng
  ((if useCell then .cell Cell.empty else .null), rng')

private def classifyRshiftHashMod (x : Int) (shift : Nat) : String :=
  let r := modPow2Round x shift (-1)
  if r = 0 then
    "ok-exact"
  else if x = 0 ∨ x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 then
    "ok-near-boundary"
  else if x = maxInt257 ∨ x = minInt257 ∨ x = maxInt257 - 1 ∨ x = minInt257 + 1 then
    "ok-boundary"
  else if shift = 256 then
    "ok-shift256"
  else if x < 0 then
    "ok-sign-neg"
  else
    "ok-sign-pos"

private def mkFiniteFuzzCase (shape : Nat) (x : Int) (shift : Nat) : OracleCase :=
  let kind := classifyRshiftHashMod x shift
  mkShiftCase s!"/fuzz/shape-{shape}/{kind}" shift #[intV x]

private def genRshiftHashModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkFiniteFuzzCase shape x shift, r3)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftMixed r2
      (mkFiniteFuzzCase shape x shift, r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkFiniteFuzzCase shape x shift, r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkFiniteFuzzCase shape x shift, r3)
    else if shape = 4 then
      let (x, r2) := pickNearBoundaryX rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkFiniteFuzzCase shape x shift, r3)
    else if shape = 5 then
      let (x, r2) := pickNearBoundaryX rng1
      (mkFiniteFuzzCase shape x 256, r2)
    else if shape = 6 then
      let (shift, r2) := pickShiftMixed rng1
      (mkFiniteFuzzCase shape 0 shift, r2)
    else if shape = 7 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty-stack" shift #[], r2)
    else if shape = 8 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/type/x-top-null" shift #[.null], r2)
    else if shape = 9 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/type/x-top-cell" shift #[.cell Cell.empty], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/pop-order/lower-null-preserved"
        shift #[.null, intV x], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/pop-order/lower-cell-preserved"
        shift #[.cell Cell.empty, intV x], r3)
    else if shape = 12 then
      let (below, r2) := pickSigned257ish rng1
      let (badX, r3) := pickNonInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/type-top-before-lower"
        shift #[intV below, badX], r4)
    else if shape = 13 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program-shift1" 1 .nan, rng1)
    else if shape = 14 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program-shift256" 256 .nan, rng1)
    else if shape = 15 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-high-before-op"
        shift (.num (maxInt257 + 1)), r2)
    else if shape = 16 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-low-before-op"
        shift (.num (minInt257 - 1)), r2)
    else if shape = 17 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-type-check"
        #[.null] #[.pushInt (.num (pow2 257)), mkRshiftHashModInstr shift], r2)
    else if shape = 18 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-underflow"
        #[] #[.pushInt (.num (-(pow2 257))), mkRshiftHashModInstr shift], r2)
    else if shape = 19 then
      (mkFiniteFuzzCase shape minInt257 256, rng1)
    else
      (mkFiniteFuzzCase shape maxInt257 256, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := rshiftHashModId
  unit := #[
    { name := "/unit/ok/floor-sign-near-boundary-invariants"
      run := do
        let checks : Array (Int × Nat × (Int × Int)) :=
          #[
            (7, 1, (3, 1)),
            (-7, 1, (-4, 1)),
            (1, 1, (0, 1)),
            (-1, 1, (-1, 1)),
            (2, 1, (1, 0)),
            (-2, 1, (-1, 0)),
            (3, 2, (0, 3)),
            (-3, 2, (-1, 1)),
            (5, 3, (0, 5)),
            (-5, 3, (-1, 3)),
            (9, 2, (2, 1)),
            (-9, 2, (-3, 3)),
            (17, 4, (1, 1)),
            (-17, 4, (-2, 15)),
            (0, 16, (0, 0))
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"/unit/ok/x={x}/shift={shift}"
            (runRshiftHashModDirect shift #[intV x]) #[intV q, intV r] }
    ,
    { name := "/unit/ok/boundary-shifts-and-signed257-extremes"
      run := do
        let checks : Array (Int × Nat × (Int × Int)) :=
          #[
            (maxInt257, 1, ((pow2 255) - 1, 1)),
            (minInt257, 1, (-(pow2 255), 0)),
            (maxInt257, 255, (1, (pow2 255) - 1)),
            (minInt257, 255, (-2, 0)),
            (maxInt257, 256, (0, maxInt257)),
            (maxInt257 - 1, 256, (0, maxInt257 - 1)),
            (minInt257, 256, (-1, 0)),
            (minInt257 + 1, 256, (-1, 1)),
            (pow2 255, 256, (0, pow2 255)),
            (-(pow2 255), 256, (-1, pow2 255))
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let q := c.2.2.1
          let r := c.2.2.2
          expectOkStack s!"/unit/boundary/x={x}/shift={shift}"
            (runRshiftHashModDirect shift #[intV x]) #[intV q, intV r] }
    ,
    { name := "/unit/pop-order/hash-immediate-preserves-lower-stack"
      run := do
        expectOkStack "/unit/pop-order/lower-null-preserved"
          (runRshiftHashModDirect 1 #[.null, intV 7]) #[.null, intV 3, intV 1]
        expectOkStack "/unit/pop-order/lower-cell-preserved"
          (runRshiftHashModDirect 2 #[.cell Cell.empty, intV (-7)])
          #[.cell Cell.empty, intV (-2), intV 1] }
    ,
    { name := "/unit/error/underflow-type-and-error-ordering"
      run := do
        expectErr "/unit/underflow/empty-stack"
          (runRshiftHashModDirect 1 #[]) .stkUnd
        expectErr "/unit/type/x-top-null"
          (runRshiftHashModDirect 1 #[.null]) .typeChk
        expectErr "/unit/type/x-top-cell"
          (runRshiftHashModDirect 1 #[.cell Cell.empty]) .typeChk
        expectErr "/unit/error-order/type-top-before-lower"
          (runRshiftHashModDirect 1 #[intV 7, .null]) .typeChk
        expectErr "/unit/error-order/type-top-before-lower-cell"
          (runRshiftHashModDirect 1 #[intV 7, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkRshiftHashModInstr 1
        let instr256 := mkRshiftHashModInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/decode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/rshift-hash-mod-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/rshift-hash-mod-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/opcode/assemble-hash-immediate-range-checked"
      run := do
        expectAssembleErr "/unit/assemble/shift0-range"
          (mkRshiftHashModInstr 0) .rangeChk
        expectAssembleErr "/unit/assemble/shift257-range"
          (mkRshiftHashModInstr 257) .rangeChk }
    ,
    { name := "/unit/dispatch/non-rshift-hash-mod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runRshiftHashModDispatchFallback #[]) #[intV 7229] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/floor/sign/pos-shift1" 1 (.num 7),
    mkShiftInputCase "/ok/floor/sign/neg-shift1" 1 (.num (-7)),
    mkShiftInputCase "/ok/floor/sign/pos-shift2" 2 (.num 9),
    mkShiftInputCase "/ok/floor/sign/neg-shift2" 2 (.num (-9)),
    mkShiftInputCase "/ok/floor/near-boundary/pos-one" 1 (.num 1),
    mkShiftInputCase "/ok/floor/near-boundary/neg-one" 1 (.num (-1)),
    mkShiftInputCase "/ok/floor/near-boundary/pos-two" 1 (.num 2),
    mkShiftInputCase "/ok/floor/near-boundary/neg-two" 1 (.num (-2)),
    mkShiftInputCase "/ok/floor/near-boundary/pos-seventeen-shift4" 4 (.num 17),
    mkShiftInputCase "/ok/floor/near-boundary/neg-seventeen-shift4" 4 (.num (-17)),
    mkShiftInputCase "/ok/floor/exact/divisible-pos-shift5" 5 (.num 1024),
    mkShiftInputCase "/ok/floor/exact/divisible-neg-shift5" 5 (.num (-1024)),
    mkShiftInputCase "/ok/floor/zero-shift128" 128 (.num 0),
    mkShiftInputCase "/ok/boundary/max-shift1" 1 (.num maxInt257),
    mkShiftInputCase "/ok/boundary/min-shift1" 1 (.num minInt257),
    mkShiftInputCase "/ok/boundary/max-shift255" 255 (.num maxInt257),
    mkShiftInputCase "/ok/boundary/min-shift255" 255 (.num minInt257),
    mkShiftInputCase "/ok/boundary/max-shift256" 256 (.num maxInt257),
    mkShiftInputCase "/ok/boundary/max-minus-one-shift256" 256 (.num (maxInt257 - 1)),
    mkShiftInputCase "/ok/boundary/min-shift256" 256 (.num minInt257),
    mkShiftInputCase "/ok/boundary/min-plus-one-shift256" 256 (.num (minInt257 + 1)),
    mkShiftInputCase "/ok/boundary/pow255-shift256" 256 (.num (pow2 255)),
    mkShiftInputCase "/ok/boundary/negpow255-shift256" 256 (.num (-(pow2 255))),
    mkShiftCase "/ok/pop-order/lower-null-preserved" 1 #[.null, intV 7],
    mkShiftCase "/ok/pop-order/lower-cell-preserved" 2 #[.cell Cell.empty, intV (-7)],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/type/x-top-null" 1 #[.null],
    mkShiftCase "/type/x-top-cell" 1 #[.cell Cell.empty],
    mkShiftCase "/error-order/type-top-before-lower" 1 #[intV 7, .null],
    mkShiftCase "/error-order/type-top-before-lower-cell" 1 #[intV 7, .cell Cell.empty],
    mkShiftInputCase "/intov/nan-x-via-program-shift1" 1 .nan,
    mkShiftInputCase "/intov/nan-x-via-program-shift256" 256 .nan,
    mkShiftInputCase "/error-order/pushint-overflow-high-before-op" 1 (.num (maxInt257 + 1)),
    mkShiftInputCase "/error-order/pushint-overflow-low-before-op" 1 (.num (minInt257 - 1)),
    mkCase "/error-order/pushint-overflow-before-op-type-check" #[.null]
      #[.pushInt (.num (pow2 257)), mkRshiftHashModInstr 1],
    mkCase "/error-order/pushint-overflow-before-op-underflow" #[]
      #[.pushInt (.num (-(pow2 257))), mkRshiftHashModInstr 1],
    mkCase "/gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num rshiftHashModSetGasExact), .tonEnvOp .setGasLimit, rshiftHashModGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num rshiftHashModSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftHashModGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020899
      count := 700
      gen := genRshiftHashModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFT_HASH_MOD
