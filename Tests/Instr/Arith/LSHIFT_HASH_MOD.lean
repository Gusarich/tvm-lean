import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFT_HASH_MOD

/-
LSHIFT#MOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 2 (-1) false false (some z)` specialization)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, floor remainder semantics)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate family `0xa9d8..0xa9da`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, hash-immediate decode family `0xa9d8..0xa9da`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, underflow/type/overflow behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite (`d=2`, `roundMode=-1`,
`add=false`, `quiet=false`, `zOpt=some z`):
- Lean specialization: 7 branch sites / 9 terminal outcomes
  (dispatch/fallback; arity gate; immediate-range gate; `y` pop type;
   `x` pop type; numeric-vs-invalid split; divisor-zero split).
- C++ specialization: 7 branch sites / 9 aligned terminal outcomes
  (`check_underflow(2)`; immediate-range gate; `pop_int` for divisor;
   `pop_int` for numerator; invalid-input funnel; divisor-zero split;
   remainder push path).

Key risk areas covered:
- hash-immediate discipline: `z` is encoded and must never be popped;
- floor remainder sign behavior for mixed signs and boundary shifts (`1`, `256`);
- strict pop/error ordering: underflow before type, and `y` popped before `x`;
- malformed-immediate precedence in direct handler (`z=0`, `z=257`);
- NaN/out-of-range injection via `PUSHINT` prelude only (oracle/fuzz serialization hygiene);
- exact gas boundary via `PUSHINT n; SETGASLIMIT; LSHIFT#MOD`.
-/

private def lshiftHashModId : InstrId := { name := "LSHIFT#MOD" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkLshiftHashModInstr (shift : Nat) : Instr :=
  .arithExt (.shlDivMod 2 (-1) false false (some shift))

private def lshiftHashModInstrDefault : Instr :=
  mkLshiftHashModInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftHashModInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := lshiftHashModId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkShiftCase
    (name : String)
    (x y : Int)
    (shift : Nat)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name #[intV x, intV y] #[mkLshiftHashModInstr shift] gasLimits fuel

private def mkShiftStackCase
    (name : String)
    (shift : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[mkLshiftHashModInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (x y : IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkLshiftHashModInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[x, y]
  mkCase name stack (progPrefix.push instr) gasLimits fuel

private def runLshiftHashModDirect (shift : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkLshiftHashModInstr shift) stack

private def runLshiftHashModDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 6411)) stack

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

private def lshiftHashModGasProbeInstr : Instr :=
  mkLshiftHashModInstr 7

private def lshiftHashModSetGasExact : Int :=
  computeExactGasBudget lshiftHashModGasProbeInstr

private def lshiftHashModSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftHashModGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def smallDivisorPool : Array Int :=
  #[-7, -5, -3, -2, -1, 1, 2, 3, 5, 7]

private def smallNumeratorPool : Array Int :=
  #[-17, -13, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 13, 17]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickFromNatPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromNatPool shiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def classifyLshiftHashMod (x y : Int) (shift : Nat) : String :=
  if y = 0 then
    "intov-divzero"
  else
    let tmp : Int := x * intPow2 shift
    let (_, r) := divModRound tmp y (-1)
    if r = 0 then
      "ok-exact"
    else if decide (y > 0) then
      "ok-inexact-pos-divisor"
    else
      "ok-inexact-neg-divisor"

private def mkFiniteFuzzCase (shape : Nat) (x y : Int) (shift : Nat) : OracleCase :=
  let kind := classifyLshiftHashMod x y shift
  mkShiftCase s!"/fuzz/shape-{shape}/{kind}" x y shift

private def genLshiftHashModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 2 then
      let (x, r2) := pickFromIntPool smallNumeratorPool rng1
      let (y, r3) := pickFromIntPool smallDivisorPool r2
      let (shift, r4) := pickShiftBoundary r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftCase s!"/fuzz/shape-{shape}/intov-divzero" x 0 shift, r3)
    else if shape = 4 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow-empty" shift #[], r2)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow-one-int" shift #[intV x], r3)
    else if shape = 6 then
      let (v, r2) := pickNonInt rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order-underflow-before-type-single-non-int"
        shift #[v], r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (yBad, r3) := pickNonInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type-pop-y-first" shift #[intV x, yBad], r4)
    else if shape = 8 then
      let (y, r2) := pickNonZeroInt rng1
      let (xBad, r3) := pickNonInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type-pop-x-second" shift #[xBad, intV y], r4)
    else if shape = 9 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order-pop-y-before-x-when-both-non-int"
        shift #[.null, .cell Cell.empty], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      let (below, r5) := pickNonInt r4
      (mkShiftStackCase s!"/fuzz/shape-{shape}/pop-order/below-preserved"
        shift #[below, intV x, intV y], r5)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-nan-y-via-program" shift (.num x) .nan, r3)
    else if shape = 12 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-nan-x-via-program" shift .nan (.num y), r3)
    else if shape = 13 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-nan-both-via-program" shift .nan .nan, r2)
    else if shape = 14 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order-pushint-overflow-x-before-op"
        shift (.num xo) (.num y), r4)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (yo, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order-pushint-overflow-y-before-op"
        shift (.num x) (.num yo), r4)
    else if shape = 16 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (yo, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order-pushint-overflow-both-before-op"
        shift (.num xo) (.num yo), r4)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickFromIntPool smallDivisorPool r2
      (mkShiftCase s!"/fuzz/shape-{shape}/boundary/shift-256" x y 256, r3)
    else if shape = 18 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickFromIntPool smallDivisorPool r2
      (mkShiftCase s!"/fuzz/shape-{shape}/boundary/shift-1" x y 1, r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftCase s!"/fuzz/shape-{shape}/exact/div-by-one" x 1 shift, r3)
    else
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftCase s!"/fuzz/shape-{shape}/exact/div-by-minus-one" x (-1) shift, r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftHashModId
  unit := #[
    { name := "/unit/direct/floor-remainder-sign-and-shift-invariants"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (7, 3, 1, 2),
            (-7, 3, 1, 1),
            (7, -3, 1, -1),
            (-7, -3, 1, -2),
            (1, 3, 2, 1),
            (-1, 3, 2, 2),
            (1, -3, 2, -2),
            (-1, -3, 2, -1),
            (0, 5, 256, 0),
            (1, maxInt257, 256, 1),
            (-1, maxInt257, 256, maxInt257 - 1),
            (1, minInt257, 256, 0),
            (-1, minInt257, 256, 0),
            (maxInt257, 2, 1, 0),
            (minInt257, 2, 1, 0),
            (minInt257 + 1, 2, 1, 0)
          ]
        for c in checks do
          match c with
          | (x, y, shift, expected) =>
              expectOkStack s!"/unit/direct/x={x}/y={y}/shift={shift}"
                (runLshiftHashModDirect shift #[intV x, intV y]) #[intV expected] }
    ,
    { name := "/unit/pop-order/hash-immediate-does-not-pop-third-item"
      run := do
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runLshiftHashModDirect 1 #[.null, intV 7, intV 3]) #[.null, intV 2]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runLshiftHashModDirect 2 #[.cell Cell.empty, intV (-7), intV 3]) #[.cell Cell.empty, intV 2] }
    ,
    { name := "/unit/error/divzero-underflow-type-and-pop-order"
      run := do
        expectErr "/unit/intov/divzero/nonzero-over-zero"
          (runLshiftHashModDirect 1 #[intV 7, intV 0]) .intOv
        expectErr "/unit/intov/divzero/zero-over-zero"
          (runLshiftHashModDirect 256 #[intV 0, intV 0]) .intOv
        expectErr "/unit/underflow/empty"
          (runLshiftHashModDirect 1 #[]) .stkUnd
        expectErr "/unit/underflow/one-int"
          (runLshiftHashModDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-single-non-int"
          (runLshiftHashModDirect 1 #[.null]) .stkUnd
        expectErr "/unit/type/pop-y-first-null"
          (runLshiftHashModDirect 1 #[intV 1, .null]) .typeChk
        expectErr "/unit/type/pop-y-first-cell"
          (runLshiftHashModDirect 1 #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "/unit/type/pop-x-second-null"
          (runLshiftHashModDirect 1 #[.null, intV 1]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-when-both-non-int"
          (runLshiftHashModDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/error/immediate-range-gate-precedence"
      run := do
        expectErr "/unit/error-order/underflow-before-range-invalid-immediate"
          (runLshiftHashModDirect 0 #[]) .stkUnd
        expectErr "/unit/error-order/range-before-x-type-invalid-immediate-low"
          (runLshiftHashModDirect 0 #[.null, intV 7]) .typeChk
        expectErr "/unit/error-order/range-before-y-type-invalid-immediate-high"
          (runLshiftHashModDirect 257 #[intV 7, .null]) .rangeChk
        expectErr "/unit/error-order/range-before-x-type-invalid-immediate-high"
          (runLshiftHashModDirect 257 #[.null, intV 7]) .rangeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkLshiftHashModInstr 1
        let instr256 := mkLshiftHashModInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/decode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/lshift-hash-mod-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/lshift-hash-mod-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-lshift-hash-mod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runLshiftHashModDispatchFallback #[]) #[intV 6411] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/floor/sign/pos-pos-shift1" 1 (.num 7) (.num 3),
    mkShiftInputCase "/ok/floor/sign/neg-pos-shift1" 1 (.num (-7)) (.num 3),
    mkShiftInputCase "/ok/floor/sign/pos-neg-shift1" 1 (.num 7) (.num (-3)),
    mkShiftInputCase "/ok/floor/sign/neg-neg-shift1" 1 (.num (-7)) (.num (-3)),
    mkShiftInputCase "/ok/floor/inexact/shift2-small" 2 (.num 1) (.num 3),
    mkShiftInputCase "/ok/floor/inexact/shift2-small-neg-x" 2 (.num (-1)) (.num 3),
    mkShiftInputCase "/ok/floor/inexact/shift2-small-neg-y" 2 (.num 1) (.num (-3)),
    mkShiftInputCase "/ok/floor/inexact/shift2-small-both-neg" 2 (.num (-1)) (.num (-3)),
    mkShiftInputCase "/ok/floor/zero-numerator-shift256" 256 (.num 0) (.num 5),
    mkShiftInputCase "/ok/boundary/max-shift1-div2" 1 (.num maxInt257) (.num 2),
    mkShiftInputCase "/ok/boundary/min-shift1-div2" 1 (.num minInt257) (.num 2),
    mkShiftInputCase "/ok/boundary/min-plus-one-shift1-div2" 1 (.num (minInt257 + 1)) (.num 2),
    mkShiftInputCase "/ok/boundary/one-shift256-div-max" 256 (.num 1) (.num maxInt257),
    mkShiftInputCase "/ok/boundary/neg-one-shift256-div-max" 256 (.num (-1)) (.num maxInt257),
    mkShiftInputCase "/ok/boundary/one-shift256-div-min" 256 (.num 1) (.num minInt257),
    mkShiftInputCase "/ok/boundary/neg-one-shift256-div-min" 256 (.num (-1)) (.num minInt257),
    mkShiftStackCase "/ok/pop-order/hash-immediate-does-not-pop-third-item-null"
      1 #[.null, intV 7, intV 3],
    mkShiftStackCase "/ok/pop-order/hash-immediate-does-not-pop-third-item-cell"
      2 #[.cell Cell.empty, intV (-7), intV 3],
    mkShiftInputCase "/intov/divzero/nonzero-over-zero" 1 (.num 7) (.num 0),
    mkShiftInputCase "/intov/divzero/zero-over-zero" 256 (.num 0) (.num 0),
    mkShiftStackCase "/underflow/empty-stack" 1 #[],
    mkShiftStackCase "/underflow/one-item" 1 #[intV 1],
    mkShiftStackCase "/error-order/underflow-before-type-single-non-int" 1 #[.null],
    mkShiftStackCase "/type/pop-y-first-null" 1 #[intV 1, .null],
    mkShiftStackCase "/type/pop-y-first-cell" 1 #[intV 1, .cell Cell.empty],
    mkShiftStackCase "/type/pop-x-second-null" 1 #[.null, intV 1],
    mkShiftStackCase "/error-order/pop-y-before-x-when-both-non-int" 1 #[.null, .cell Cell.empty],
    mkShiftInputCase "/intov/nan-y-via-program" 1 (.num 7) .nan,
    mkShiftInputCase "/intov/nan-x-via-program" 1 .nan (.num 3),
    mkShiftInputCase "/intov/nan-both-via-program" 1 .nan .nan,
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op"
      1 (.num (maxInt257 + 1)) (.num 3),
    mkShiftInputCase "/error-order/pushint-overflow-y-before-op"
      1 (.num 7) (.num (maxInt257 + 1)),
    mkShiftInputCase "/error-order/pushint-overflow-both-before-op"
      1 (.num (maxInt257 + 1)) (.num (minInt257 - 1)),
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num lshiftHashModSetGasExact), .tonEnvOp .setGasLimit, lshiftHashModGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num lshiftHashModSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftHashModGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020863
      count := 700
      gen := genLshiftHashModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFT_HASH_MOD
