import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFT_HASH_DIVMODR

/-
LSHIFT#DIVMODR branch-map notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 3 0 false false (some z)` specialization)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate `0xa9dc..0xa9de` family)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, hash-immediate decode to `.shlDivMod`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, nearest mode with ties toward `+∞`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type/overflow behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`mod_div`, nearest rounding quotient/remainder)

Branch/terminal counts used for this suite
(`d=3`, `roundMode=0`, `addMode=false`, `quiet=false`, `zOpt=some z` specialization):
- Lean: 9 branch sites / 11 terminal outcomes
  (dispatch/fallback; underflow gate; immediate-shift range gate; `y` pop type;
   `x` pop type; numeric-vs-invalid split; divisor-zero split; nearest-division
   path; dual-push funnel with non-quiet `intOv`).
- C++: 8 branch sites / 11 aligned terminal outcomes
  (`check_underflow(2)` for hash-immediate path; opcode-arg validation guard;
   `pop_int` for divisor/numerator; invalid-input funnel; divisor-zero split;
   nearest `mod_div` path and push fit-vs-overflow funnel).

Key risk areas covered:
- nearest rounding ties toward `+∞` for `(x << z) / y`, with correct `(q, r)` order;
- hash-immediate behavior (`z` encoded in opcode, never popped from stack);
- explicit pop/error ordering (`y` then `x`, with underflow before type);
- malformed immediate range gate precedence in direct-handler tests (`z=0`, `z=257`);
- non-quiet `intOv` funnels (div-by-zero, NaN via prelude, quotient overflow);
- NaN/out-of-range oracle injections only through program prelude (`PUSHINT*`);
- exact gas cliff (`PUSHINT n; SETGASLIMIT; LSHIFT#DIVMODR`).
-/

private def lshiftHashDivmodrId : InstrId := { name := "LSHIFT#DIVMODR" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkLshiftHashDivmodrInstr (shift : Nat) : Instr :=
  .arithExt (.shlDivMod 3 0 false false (some shift))

private def lshiftHashDivmodrInstrDefault : Instr :=
  mkLshiftHashDivmodrInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftHashDivmodrInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := lshiftHashDivmodrId
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
  mkCase name #[intV x, intV y] #[mkLshiftHashDivmodrInstr shift] gasLimits fuel

private def mkInputCase
    (name : String)
    (x y : IntVal)
    (shift : Nat := 1)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[x, y]
  mkCase name stack (progPrefix.push (mkLshiftHashDivmodrInstr shift)) gasLimits fuel

private def runLshiftHashDivmodrDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkLshiftHashDivmodrInstr shift) stack

private def runLshiftHashDivmodrDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 4962)) stack

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

private def expectLshiftHashDivmodr
    (label : String)
    (x y : Int)
    (shift : Nat)
    (q r : Int) : IO Unit :=
  expectOkStack label
    (runLshiftHashDivmodrDirect shift #[intV x, intV y])
    #[intV q, intV r]

private def lshiftHashDivmodrGasProbeInstr : Instr :=
  mkLshiftHashDivmodrInstr 7

private def lshiftHashDivmodrSetGasExact : Int :=
  computeExactGasBudget lshiftHashDivmodrGasProbeInstr

private def lshiftHashDivmodrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftHashDivmodrGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieNumeratorPool : Array Int :=
  #[-15, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11, 13, 15]

private def tieDenominatorPool : Array Int :=
  #[-2, 2]

private def smallDivisorPool : Array Int :=
  #[-7, -5, -3, -2, -1, 1, 2, 3, 5, 7]

private def outOfRangeProgramPool : Array Int :=
  #[maxInt257 + 1, minInt257 - 1, pow2 257, -(pow2 257)]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickFromNatPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickValidShift (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickFromNatPool shiftBoundaryPool rng1
  else
    randNat rng1 1 256

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (n, rng1) := pickSigned257ish rng0
  (if n = 0 then 1 else n, rng1)

private def pickOutOfRangeProgramInt (rng : StdGen) : Int × StdGen :=
  pickFromIntPool outOfRangeProgramPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  (if pickCell then .cell Cell.empty else .null, rng')

private def classifyLshiftHashDivmodr (x y : Int) (shift : Nat) : String :=
  if y = 0 then
    "intov-divzero"
  else
    let tmp : Int := x * intPow2 shift
    let (q, r) := divModRound tmp y 0
    if !intFitsSigned257 q || !intFitsSigned257 r then
      "intov-overflow"
    else if r = 0 then
      "ok-exact"
    else if (Int.natAbs r) * 2 = Int.natAbs y then
      "ok-tie"
    else
      "ok-inexact"

private def mkFiniteFuzzCase (shape : Nat) (x y : Int) (shift : Nat) : OracleCase :=
  let kind := classifyLshiftHashDivmodr x y shift
  mkShiftCase s!"/fuzz/shape-{shape}/{kind}" x y shift

private def genLshiftHashDivmodrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 23
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickFromNatPool shiftBoundaryPool r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickValidShift r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 2 then
      let (x, r2) := pickFromIntPool tieNumeratorPool rng1
      let (y, r3) := pickFromIntPool tieDenominatorPool r2
      (mkFiniteFuzzCase shape x y 1, r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkShiftCase s!"/fuzz/shape-{shape}/intov-divzero" x 0 shift, r3)
    else if shape = 4 then
      (mkShiftCase s!"/fuzz/shape-{shape}/intov-overflow/max-shift1-div1"
        maxInt257 1 1, rng1)
    else if shape = 5 then
      (mkShiftCase s!"/fuzz/shape-{shape}/intov-overflow/min-shift1-div1"
        minInt257 1 1, rng1)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty-stack" #[], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-item" #[intV x], r2)
    else if shape = 8 then
      let (v, r2) := pickNonInt rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type-single-non-int" #[v], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-first"
        #[intV x, yLike], r3)
    else if shape = 10 then
      let (y, r2) := pickNonZeroInt rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-second"
        #[xLike, intV y], r3)
    else if shape = 11 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-when-both-non-int"
        #[.null, .cell Cell.empty], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickValidShift r3
      let (belowCell, r5) := randBool r4
      let below : Value := if belowCell then .cell Cell.empty else .null
      (mkCase s!"/fuzz/shape-{shape}/pop-order/hash-immediate-does-not-pop-third-item"
        #[below, intV x, intV y] #[mkLshiftHashDivmodrInstr shift], r5)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkInputCase s!"/fuzz/shape-{shape}/intov/nan-divisor-via-program"
        (.num x) .nan shift, r3)
    else if shape = 14 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickValidShift r2
      (mkInputCase s!"/fuzz/shape-{shape}/intov/nan-numerator-via-program"
        .nan (.num y) shift, r3)
    else if shape = 15 then
      let (shift, r2) := pickValidShift rng1
      (mkInputCase s!"/fuzz/shape-{shape}/intov/nan-both-via-program"
        .nan .nan shift, r2)
    else if shape = 16 then
      let (x, r2) := pickNonZeroInt rng1
      let (y, r3) := pickOutOfRangeProgramInt r2
      let (shift, r4) := pickValidShift r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        (.num x) (.num y) shift, r4)
    else if shape = 17 then
      let (x, r2) := pickOutOfRangeProgramInt rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickValidShift r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        (.num x) (.num y) shift, r4)
    else if shape = 18 then
      let (x, r2) := pickOutOfRangeProgramInt rng1
      let (y, r3) := pickOutOfRangeProgramInt r2
      let (shift, r4) := pickValidShift r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-both-before-op"
        (.num x) (.num y) shift, r4)
    else if shape = 19 then
      let (x, r2) := pickFromIntPool #[-1, 0, 1] rng1
      let (y, r3) := pickFromIntPool smallDivisorPool r2
      (mkFiniteFuzzCase shape x y 256, r3)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/ok-exact/div-by-one" x 1 1, r2)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/ok-exact/div-by-neg-one" x (-1) 1, r2)
    else if shape = 22 then
      (mkShiftCase s!"/fuzz/shape-{shape}/ok-tie/near-zero" (-1) 4 1, rng1)
    else
      (mkShiftCase s!"/fuzz/shape-{shape}/intov/divzero-shift256" 7 0 256, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftHashDivmodrId
  unit := #[
    { name := "/unit/ok/nearest-rounding-sign-tie-and-output-order"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (7, 3, 1, 5, -1),
            (-7, 3, 1, -5, 1),
            (7, -3, 1, -5, -1),
            (-7, -3, 1, 5, 1),
            (5, 4, 1, 3, -2),
            (-5, 4, 1, -2, -2),
            (5, -4, 1, -2, 2),
            (-5, -4, 1, 3, 2),
            (1, 4, 1, 1, -2),
            (-1, 4, 1, 0, -2),
            (1, -4, 1, 0, 2),
            (-1, -4, 1, 1, 2),
            (7, 5, 2, 6, -2),
            (-7, 5, 2, -6, 2),
            (7, -5, 2, -6, -2),
            (-7, -5, 2, 6, 2),
            (42, 7, 3, 48, 0),
            (0, 5, 8, 0, 0)
          ]
        for c in checks do
          match c with
          | (x, y, shift, q, r) =>
              expectLshiftHashDivmodr s!"/unit/ok/x={x}/y={y}/z={shift}" x y shift q r }
    ,
    { name := "/unit/ok/boundary-success-and-hash-pop-order"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (maxInt257, 2, 1, maxInt257, 0),
            (maxInt257, 4, 1, pow2 255, -2),
            (minInt257, 2, 1, minInt257, 0),
            (minInt257, 4, 1, -(pow2 255), 0),
            (minInt257 + 1, -2, 1, maxInt257, 0),
            (1, maxInt257, 256, 1, 1),
            (-1, maxInt257, 256, -1, -1),
            (1, minInt257, 256, -1, 0),
            (-1, minInt257, 256, 1, 0),
            (0, 3, 256, 0, 0)
          ]
        for c in checks do
          match c with
          | (x, y, shift, q, r) =>
              expectLshiftHashDivmodr s!"/unit/boundary/x={x}/y={y}/z={shift}" x y shift q r
        expectOkStack "/unit/pop-order/hash-immediate-does-not-pop-third-item/null"
          (runLshiftHashDivmodrDirect 1 #[.null, intV 7, intV 3])
          #[.null, intV 5, intV (-1)]
        expectOkStack "/unit/pop-order/hash-immediate-does-not-pop-third-item/cell"
          (runLshiftHashDivmodrDirect 2 #[.cell Cell.empty, intV (-7), intV 3])
          #[.cell Cell.empty, intV (-9), intV (-1)] }
    ,
    { name := "/unit/error/intov-divzero-and-overflow-funnels"
      run := do
        expectErr "/unit/intov/divzero/nonzero-over-zero"
          (runLshiftHashDivmodrDirect 1 #[intV 7, intV 0]) .intOv
        expectErr "/unit/intov/divzero/zero-over-zero"
          (runLshiftHashDivmodrDirect 256 #[intV 0, intV 0]) .intOv
        expectErr "/unit/intov/overflow/max-shift1-div1"
          (runLshiftHashDivmodrDirect 1 #[intV maxInt257, intV 1]) .intOv
        expectErr "/unit/intov/overflow/min-shift1-div1"
          (runLshiftHashDivmodrDirect 1 #[intV minInt257, intV 1]) .intOv }
    ,
    { name := "/unit/error/underflow-pop-order-and-type-order"
      run := do
        expectErr "/unit/underflow/empty"
          (runLshiftHashDivmodrDirect 1 #[]) .stkUnd
        expectErr "/unit/underflow/one-int"
          (runLshiftHashDivmodrDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/underflow/one-non-int-underflow-before-type"
          (runLshiftHashDivmodrDirect 1 #[.null]) .stkUnd
        expectErr "/unit/type/pop-y-first-null"
          (runLshiftHashDivmodrDirect 1 #[intV 1, .null]) .typeChk
        expectErr "/unit/type/pop-y-first-cell"
          (runLshiftHashDivmodrDirect 1 #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "/unit/type/pop-x-second-null"
          (runLshiftHashDivmodrDirect 1 #[.null, intV 1]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-when-both-non-int"
          (runLshiftHashDivmodrDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/error/immediate-range-gate-precedence"
      run := do
        let invalidLow : Instr := .arithExt (.shlDivMod 3 0 false false (some 0))
        let invalidHigh : Instr := .arithExt (.shlDivMod 3 0 false false (some 257))
        expectErr "/unit/error-order/underflow-before-range-invalid-immediate"
          (runHandlerDirect execInstrArithExt invalidLow #[]) .stkUnd
        expectErr "/unit/error-order/range-before-y-type-invalid-immediate-low"
          (runHandlerDirect execInstrArithExt invalidLow #[intV 7, .null]) .rangeChk
        expectErr "/unit/error-order/range-before-x-type-invalid-immediate-high"
          (runHandlerDirect execInstrArithExt invalidHigh #[.null, intV 7]) .rangeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkLshiftHashDivmodrInstr 1
        let instr256 := mkLshiftHashDivmodrInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/decode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/lshift-hash-divmodr-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/lshift-hash-divmodr-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-lshift-hash-divmodr-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runLshiftHashDivmodrDispatchFallback #[]) #[intV 4962] }
  ]
  oracle := #[
    mkShiftCase "/ok/round/inexact-pos-pos-shift1" 7 3 1,
    mkShiftCase "/ok/round/inexact-neg-pos-shift1" (-7) 3 1,
    mkShiftCase "/ok/round/inexact-pos-neg-shift1" 7 (-3) 1,
    mkShiftCase "/ok/round/inexact-neg-neg-shift1" (-7) (-3) 1,
    mkShiftCase "/ok/tie/pos-over-pos-four-shift1-wide" 5 4 1,
    mkShiftCase "/ok/tie/neg-over-pos-four-shift1-wide" (-5) 4 1,
    mkShiftCase "/ok/tie/pos-over-neg-four-shift1-wide" 5 (-4) 1,
    mkShiftCase "/ok/tie/neg-over-neg-four-shift1-wide" (-5) (-4) 1,
    mkShiftCase "/ok/tie/pos-over-pos-four-shift1" 1 4 1,
    mkShiftCase "/ok/tie/neg-over-pos-four-shift1" (-1) 4 1,
    mkShiftCase "/ok/tie/pos-over-neg-four-shift1" 1 (-4) 1,
    mkShiftCase "/ok/tie/neg-over-neg-four-shift1" (-1) (-4) 1,
    mkShiftCase "/ok/exact/shift3-pos-pos" 42 7 3,
    mkShiftCase "/ok/exact/shift3-neg-pos" (-42) 7 3,
    mkShiftCase "/ok/exact/shift3-pos-neg" 42 (-7) 3,
    mkShiftCase "/ok/exact/shift3-neg-neg" (-42) (-7) 3,
    mkShiftCase "/ok/exact/zero-numerator-shift8" 0 5 8,
    mkShiftCase "/ok/boundary/max-shift1-div2" maxInt257 2 1,
    mkShiftCase "/ok/boundary/min-shift1-div2" minInt257 2 1,
    mkShiftCase "/ok/boundary/min-plus-one-shift1-div-neg2" (minInt257 + 1) (-2) 1,
    mkShiftCase "/ok/boundary/one-shift256-div-max" 1 maxInt257 256,
    mkShiftCase "/ok/boundary/neg-one-shift256-div-max" (-1) maxInt257 256,
    mkShiftCase "/ok/boundary/one-shift256-div-min" 1 minInt257 256,
    mkShiftCase "/ok/boundary/neg-one-shift256-div-min" (-1) minInt257 256,
    mkCase "/ok/pop-order/hash-immediate-does-not-pop-third-item"
      #[.null, intV 7, intV 3] #[mkLshiftHashDivmodrInstr 1],
    mkShiftCase "/intov/divzero/nonzero-over-zero" 7 0 1,
    mkShiftCase "/intov/divzero/zero-over-zero" 0 0 256,
    mkShiftCase "/intov/overflow/max-shift1-div1" maxInt257 1 1,
    mkShiftCase "/intov/overflow/min-shift1-div1" minInt257 1 1,
    mkCase "/underflow/empty-stack" #[] #[lshiftHashDivmodrInstrDefault],
    mkCase "/underflow/one-int" #[intV 1] #[lshiftHashDivmodrInstrDefault],
    mkCase "/error-order/underflow-before-type-single-non-int" #[.null] #[lshiftHashDivmodrInstrDefault],
    mkCase "/type/pop-y-first-null" #[intV 1, .null] #[lshiftHashDivmodrInstrDefault],
    mkCase "/type/pop-y-first-cell" #[intV 1, .cell Cell.empty] #[lshiftHashDivmodrInstrDefault],
    mkCase "/type/pop-x-second-null" #[.null, intV 1] #[lshiftHashDivmodrInstrDefault],
    mkCase "/error-order/pop-y-before-x-when-both-non-int" #[.null, .cell Cell.empty] #[lshiftHashDivmodrInstrDefault],
    mkInputCase "/intov/nan-divisor-via-program" (.num 7) .nan 1,
    mkInputCase "/intov/nan-numerator-via-program" .nan (.num 3) 1,
    mkInputCase "/error-order/pushint-overflow-x-before-op" (.num (maxInt257 + 1)) (.num 3) 1,
    mkInputCase "/error-order/pushint-overflow-y-before-op" (.num 7) (.num (maxInt257 + 1)) 1,
    mkInputCase "/error-order/pushint-overflow-both-before-op"
      (.num (pow2 257)) (.num (-(pow2 257))) 1,
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num lshiftHashDivmodrSetGasExact), .tonEnvOp .setGasLimit, lshiftHashDivmodrGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num lshiftHashDivmodrSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftHashDivmodrGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020891
      count := 700
      gen := genLshiftHashDivmodrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFT_HASH_DIVMODR
