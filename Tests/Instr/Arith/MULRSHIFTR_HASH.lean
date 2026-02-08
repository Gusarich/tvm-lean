import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULRSHIFTR_HASH

/-
MULRSHIFTR# branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulShrModConst.lean`
    (`execInstrArithMulShrModConst`, `.mulShrModConst 1 0 z` specialization)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, `0xa9b***` → `.mulShrModConst d roundMode z`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`, underflow/type/overflow behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, const-shift (`imm`) MUL*RSHIFT family behavior)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean hash-const specialization (`d=1`, `roundMode=0`, `z ∈ [1,256]`):
  6 branch sites / 7 terminal outcomes
  (dispatch/fallback; underflow gate; y/x pop type split; numeric-vs-NaN split;
   `d` arm; non-quiet push success-vs-`intOv`).
- C++ aligned specialization: 6 branch sites / 7 terminal outcomes
  (opcode route; underflow gate; y/x pop/type split; const-shift arithmetic arm;
   result push fit-vs-`int_ov`).

Key risk areas covered:
- nearest rounding ties go to `+∞` after multiplication;
- boundary magnitudes around signed-257 limits with `z=1`, `z=255`, `z=256`;
- pop order is `y` then `x` (hash immediate means no runtime shift pop);
- NaN/out-of-range integer injection is program-only (`PUSHINT`) in oracle/fuzz;
- overflow funnel (`intOv`) from both NaN and oversized quotient;
- exact gas cliff (`PUSHINT n; SETGASLIMIT; ...`) with exact and exact-minus-one.

Implementation note:
- Oracle/fuzz cases use an executable equivalent program shape:
  `PUSHINT z; MULRSHIFTR` (`.shrMod true false 1 0 false none`).
-/

private def mulrshiftrHashId : InstrId := { name := "MULRSHIFTR#" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkMulrshiftrHashInstr (shift : Nat) : Instr :=
  .mulShrModConst 1 0 shift

private def mulrshiftrCompatInstr : Instr :=
  .arithExt (.shrMod true false 1 0 false none)

private def mkCompatProgram (shift : Nat) : Array Instr :=
  #[.pushInt (.num (Int.ofNat shift)), mulrshiftrCompatInstr]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := mulrshiftrHashId
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
  mkCase name stack (mkCompatProgram shift) gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (programPrefix ++ mkCompatProgram shift) gasLimits fuel

private def runMulrshiftrHashDirect (shift : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulShrModConst (mkMulrshiftrHashInstr shift) stack

private def runMulrshiftrCompatDirect (shift : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt mulrshiftrCompatInstr (stack.push (intV (Int.ofNat shift)))

private def runMulrshiftrHashDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulShrModConst .add (VM.push (intV 9445)) stack

private def expectSameStackResult
    (label : String)
    (lhs rhs : Except Excno (Array Value)) : IO Unit := do
  match lhs, rhs with
  | .ok xs, .ok ys =>
      if xs == ys then
        pure ()
      else
        throw (IO.userError s!"{label}: expected equal stacks, got {reprStr xs} vs {reprStr ys}")
  | .error e1, .error e2 =>
      if e1 == e2 then
        pure ()
      else
        throw (IO.userError s!"{label}: expected equal errors, got {e1} vs {e2}")
  | .ok xs, .error e =>
      throw (IO.userError s!"{label}: lhs ok {reprStr xs}, rhs error {e}")
  | .error e, .ok ys =>
      throw (IO.userError s!"{label}: lhs error {e}, rhs ok {reprStr ys}")

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

private def mulrshiftrHashWord24 (shift : Nat) : Except String Nat := do
  if shift = 0 ∨ shift > 256 then
    throw s!"MULRSHIFTR# raw word: shift {shift} outside [1,256]"
  let cfg4 : Nat := (1 <<< 2) + 1
  pure (((0xa9b : Nat) <<< 12) + (cfg4 <<< 8) + (shift - 1))

private def mulrshiftrHashGasProbeInstr : Instr :=
  mulrshiftrCompatInstr

private def mulrshiftrHashSetGasExact : Int :=
  computeExactGasBudget mulrshiftrHashGasProbeInstr

private def mulrshiftrHashSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulrshiftrHashGasProbeInstr

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieFactorPool : Array Int :=
  #[-17, -13, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 13, 17]

private def smallSignedPool : Array Int :=
  #[-33, -17, -13, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 13, 17, 33]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 1 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def classifyMulrshiftrHash (x y : Int) (shift : Nat) : String :=
  let product := x * y
  let q := rshiftPow2Round product shift 0
  if !intFitsSigned257 q then
    "intov"
  else
    let r := modPow2Round product shift 0
    if product = 0 then
      "ok-zero"
    else if r = 0 then
      "ok-exact"
    else
      "ok-inexact"

private def genMulrshiftrHashFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyMulrshiftrHash x y shift
      (mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}/boundary-x-boundary-y-boundary-z"
        shift #[.num x, .num y], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyMulrshiftrHash x y shift
      (mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}/random-x-random-y-random-z"
        shift #[.num x, .num y], r4)
    else if shape = 2 then
      let (x, r2) := pickFromPool tieFactorPool rng1
      let (y, r3) := pickFromPool tieFactorPool r2
      let kind := classifyMulrshiftrHash x y 1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}/nearest-tie-shift1"
        1 #[.num x, .num y], r3)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (negY, r3) := randBool r2
      let y : Int := if negY then -1 else 1
      let kind := classifyMulrshiftrHash x y 256
      (mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift256-y-sign"
        256 #[.num x, .num y], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/pop-order/lower-null-preserved"
        shift #[.null, intV x, intV y], r4)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/pop-order/lower-cell-preserved"
        shift #[.cell Cell.empty, intV x, intV y], r4)
    else if shape = 6 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty" shift #[], r2)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/one-item" shift #[intV x], r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (bad, r3) := pickNonInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/pop-y-first-top-non-int"
        shift #[intV x, bad], r4)
    else if shape = 9 then
      let (y, r2) := pickSigned257ish rng1
      let (bad, r3) := pickNonInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/pop-x-second-top-non-int"
        shift #[bad, intV y], r4)
    else if shape = 10 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/overflow-max-max-shift1"
        1 #[.num maxInt257, .num maxInt257], rng1)
    else if shape = 11 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/overflow-min-min-shift1"
        1 #[.num minInt257, .num minInt257], rng1)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program"
        shift #[.nan, .num y], r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-y-via-program"
        shift #[.num x, .nan], r3)
    else if shape = 14 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        shift #[.num xOut, .num y], r4)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op-type-check"
        shift #[.num x, .num yOut] #[.null], r4)
    else if shape = 16 then
      let (pickMax, r2) := randBool rng1
      let (negY, r3) := randBool r2
      let x := if pickMax then maxInt257 else minInt257
      let y : Int := if negY then -1 else 1
      let kind := classifyMulrshiftrHash x y 1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift1-extremes"
        1 #[.num x, .num y], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyMulrshiftrHash x y 255
      (mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift255"
        255 #[.num x, .num y], r3)
    else if shape = 18 then
      let (x, r2) := pickFromPool smallSignedPool rng1
      let (y, r3) := pickFromPool smallSignedPool r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyMulrshiftrHash x y shift
      (mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}/small-signed-mixed"
        shift #[.num x, .num y], r4)
    else
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok-zero/zero-left-factor"
        shift #[.num 0, .num y], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulrshiftrHashId
  unit := #[
    { name := "/unit/direct/nearest-rounding-sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (7, 3, 1, 11),
            (-7, 3, 1, -10),
            (7, -3, 1, -10),
            (-7, -3, 1, 11),
            (1, 1, 1, 1),
            (-1, 1, 1, 0),
            (3, 3, 2, 2),
            (-3, 3, 2, -2),
            (9, 5, 3, 6),
            (-9, 5, 3, -6),
            (9, -5, 3, -6),
            (-9, -5, 3, 6)
          ]
        for check in checks do
          match check with
          | (x, y, shift, expected) =>
              expectOkStack s!"/unit/direct/x={x}/y={y}/z={shift}"
                (runMulrshiftrHashDirect shift #[intV x, intV y]) #[intV expected] }
    ,
    { name := "/unit/direct/boundary-and-pop-order"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (maxInt257, 1, 256, 1),
            (maxInt257, -1, 256, -1),
            (minInt257, 1, 256, -1),
            (minInt257, -1, 256, 1),
            (pow2 255, 1, 256, 1),
            (-(pow2 255), 1, 256, 0),
            (maxInt257, 1, 255, 2),
            (minInt257, 1, 255, -2),
            (maxInt257 - 1, 1, 256, 1),
            (minInt257 + 1, 1, 256, -1)
          ]
        for check in checks do
          match check with
          | (x, y, shift, expected) =>
              expectOkStack s!"/unit/boundary/x={x}/y={y}/z={shift}"
                (runMulrshiftrHashDirect shift #[intV x, intV y]) #[intV expected]
        expectOkStack "/unit/pop-order/lower-null-preserved"
          (runMulrshiftrHashDirect 1 #[.null, intV 7, intV 3]) #[.null, intV 11]
        expectOkStack "/unit/pop-order/lower-cell-preserved"
          (runMulrshiftrHashDirect 1 #[.cell Cell.empty, intV (-7), intV 3])
          #[.cell Cell.empty, intV (-10)] }
    ,
    { name := "/unit/direct/compat-runtime-shim-parity"
      run := do
        let checks : Array (Int × Int × Nat) :=
          #[
            (7, 3, 1),
            (-7, 3, 1),
            (9, 5, 3),
            (maxInt257, 1, 256),
            (minInt257, -1, 256),
            (pow2 255, 1, 256),
            (-(pow2 255), 1, 256)
          ]
        for check in checks do
          match check with
          | (x, y, shift) =>
              expectSameStackResult s!"/unit/compat/x={x}/y={y}/z={shift}"
                (runMulrshiftrHashDirect shift #[intV x, intV y])
                (runMulrshiftrCompatDirect shift #[intV x, intV y]) }
    ,
    { name := "/unit/error/underflow-type-pop-order-and-intov"
      run := do
        expectErr "/unit/error/underflow-empty"
          (runMulrshiftrHashDirect 1 #[]) .stkUnd
        expectErr "/unit/error/underflow-one-item"
          (runMulrshiftrHashDirect 1 #[intV 7]) .stkUnd
        expectErr "/unit/error/type/pop-y-first-top-null"
          (runMulrshiftrHashDirect 1 #[intV 7, .null]) .typeChk
        expectErr "/unit/error/type/pop-x-second-top-null"
          (runMulrshiftrHashDirect 1 #[.null, intV 7]) .typeChk
        expectErr "/unit/error/intov/overflow-max-max-shift1"
          (runMulrshiftrHashDirect 1 #[intV maxInt257, intV maxInt257]) .intOv
        expectErr "/unit/error/intov/overflow-min-min-shift1"
          (runMulrshiftrHashDirect 1 #[intV minInt257, intV minInt257]) .intOv }
    ,
    { name := "/unit/opcode/decode-raw-hash-immediate-sequence"
      run := do
        let word1 ←
          match mulrshiftrHashWord24 1 with
          | .ok w => pure w
          | .error msg => throw (IO.userError s!"/unit/opcode/word-z1: {msg}")
        let word256 ←
          match mulrshiftrHashWord24 256 with
          | .ok w => pure w
          | .error msg => throw (IO.userError s!"/unit/opcode/word-z256: {msg}")
        let bits := natToBits word1 24 ++ natToBits word256 24 ++ natToBits 0xa0 8
        let s0 := Slice.ofCell (Cell.mkOrdinary bits #[])
        let s1 ← expectDecodeStep "/unit/opcode/decode/mulrshiftr-hash-z1"
          s0 (mkMulrshiftrHashInstr 1) 24
        let s2 ← expectDecodeStep "/unit/opcode/decode/mulrshiftr-hash-z256"
          s1 (mkMulrshiftrHashInstr 256) 24
        let s3 ← expectDecodeStep "/unit/opcode/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/opcode/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-mulrshiftr-hash-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runMulrshiftrHashDispatchFallback #[]) #[intV 9445] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/round/sign/pos-pos-shift1-half-up" 1 #[.num 7, .num 3],
    mkShiftInputCase "/ok/round/sign/neg-pos-shift1-half-up-to-plus-inf" 1 #[.num (-7), .num 3],
    mkShiftInputCase "/ok/round/sign/pos-neg-shift1-half-up-to-plus-inf" 1 #[.num 7, .num (-3)],
    mkShiftInputCase "/ok/round/sign/neg-neg-shift1-half-up" 1 #[.num (-7), .num (-3)],
    mkShiftInputCase "/ok/round/tie/plus-half" 1 #[.num 1, .num 1],
    mkShiftInputCase "/ok/round/tie/minus-half-to-plus-inf" 1 #[.num (-1), .num 1],
    mkShiftInputCase "/ok/round/tie/plus-three-halves" 1 #[.num 3, .num 1],
    mkShiftInputCase "/ok/round/tie/minus-three-halves" 1 #[.num (-3), .num 1],
    mkShiftInputCase "/ok/round/non-tie-shift3-pos" 3 #[.num 9, .num 5],
    mkShiftInputCase "/ok/round/non-tie-shift3-neg" 3 #[.num (-9), .num 5],

    mkShiftInputCase "/ok/boundary/max-times-one-shift256" 256 #[.num maxInt257, .num 1],
    mkShiftInputCase "/ok/boundary/max-times-neg-one-shift256" 256 #[.num maxInt257, .num (-1)],
    mkShiftInputCase "/ok/boundary/min-times-one-shift256" 256 #[.num minInt257, .num 1],
    mkShiftInputCase "/ok/boundary/min-times-neg-one-shift256" 256 #[.num minInt257, .num (-1)],
    mkShiftInputCase "/ok/boundary/pow255-times-one-shift256" 256 #[.num (pow2 255), .num 1],
    mkShiftInputCase "/ok/boundary/negpow255-times-one-shift256" 256 #[.num (-(pow2 255)), .num 1],
    mkShiftInputCase "/ok/boundary/max-times-one-shift255" 255 #[.num maxInt257, .num 1],
    mkShiftInputCase "/ok/boundary/min-times-one-shift255" 255 #[.num minInt257, .num 1],

    mkShiftCase "/ok/pop-order/lower-null-preserved" 1 #[.null, intV 7, intV 3],
    mkShiftCase "/ok/pop-order/lower-cell-preserved" 1 #[.cell Cell.empty, intV (-7), intV 3],
    mkShiftCase "/ok/pop-order/lower-int-preserved" 3 #[intV 42, intV 9, intV 5],

    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/underflow/one-item" 1 #[intV 7],
    mkShiftCase "/type/pop-y-first-top-null" 1 #[intV 7, .null],
    mkShiftCase "/type/pop-y-first-top-cell" 1 #[intV 7, .cell Cell.empty],
    mkShiftCase "/type/pop-x-second-top-null" 1 #[.null, intV 7],

    mkShiftInputCase "/intov/overflow-max-max-shift1" 1 #[.num maxInt257, .num maxInt257],
    mkShiftInputCase "/intov/overflow-min-min-shift1" 1 #[.num minInt257, .num minInt257],
    mkShiftInputCase "/intov/nan-x-via-program" 7 #[.nan, .num 5],
    mkShiftInputCase "/intov/nan-y-via-program" 7 #[.num 5, .nan],
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op"
      7 #[.num (maxInt257 + 1), .num 5],
    mkShiftInputCase "/error-order/pushint-overflow-y-before-op"
      7 #[.num 5, .num (minInt257 - 1)],
    mkShiftInputCase "/error-order/pushint-overflow-before-op-type-check"
      7 #[.num (pow2 257), .num 5] #[.null],

    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 13]
      #[.pushInt (.num mulrshiftrHashSetGasExact), .tonEnvOp .setGasLimit, mulrshiftrCompatInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 13]
      #[.pushInt (.num mulrshiftrHashSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulrshiftrCompatInstr]
  ]
  fuzz := #[
    { seed := 2026020859
      count := 700
      gen := genMulrshiftrHashFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFTR_HASH
