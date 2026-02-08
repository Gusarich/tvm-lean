import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULADDRSHIFTC_HASH_MOD

/-
MULADDRSHIFTC#MOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true true 3 1 false (some z)` hash-immediate path)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate add+mul shr/mod family `0xa9b0..0xa9b2`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, `0xa9b0..0xa9b2` decode to `.shrMod true true 3 ... (some z)`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`, underflow/type and non-quiet overflow behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, add+mul with const shift and ceiling rounding)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`mul=true`, `add=true`, `d=3`, `roundMode=1`, `quiet=false`, `zOpt=some z`):
- Lean specialization: ~8 branch sites / ~11 terminal outcomes
  (dispatch/fallback; depth gate; pop type ordering `w→y→x`; numeric-vs-invalid split;
   quotient and remainder push fit-vs-`intOv`).
- C++ specialization: ~8 branch sites / ~11 aligned terminal outcomes
  (`check_underflow(3)`; const-shift decode route; ordered pops `w→y→x`;
   invalid-input funnel; quotient/remainder push fit-vs-overflow).

Shared helper usage:
- `Tests.Harness.Gen.Arith` for signed-257 generators/pools,
  prelude-only NaN/out-of-range injection (`oracleIntInputsToStackOrProgram`),
  and exact gas-budget helpers.

Key risk areas covered:
- hash-immediate semantics and pop-order (`w`, then `y`, then `x`, with no runtime shift pop);
- ceiling-rounding tie behavior with signed-variation and exact/non-exact matrices;
- immediate shift boundaries (`1`, `256`) and signed-257 edge values;
- deterministic non-quiet overflow (`intOv`) from large combined intermediates;
- exact gas cliff (`exact` vs `exact-minus-one`) in oracle path;
- NaN/out-of-range injection only via prelude program prefixes.
-/

private def muladdrshiftcHashModId : InstrId := { name := "MULADDRSHIFTC#MOD" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkMuladdrshiftcHashModInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod true true 3 1 false (some shift))

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := muladdrshiftcHashModId
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
  mkCase name stack #[mkMuladdrshiftcHashModInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkMuladdrshiftcHashModInstr shift
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (programPrefix.push instr) gasLimits fuel

private def runMuladdrshiftcHashModDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkMuladdrshiftcHashModInstr shift) stack

private def runMuladdrshiftcHashModDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9419)) stack

private def expectDecodeStep
    (label : String)
    (slice : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits slice with
  | .error err =>
      throw (IO.userError s!"{label}: decode failed with {err}")
  | .ok (instr, bits, slice') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure slice'

private def muladdrshiftcHashModGasProbeInstr : Instr :=
  mkMuladdrshiftcHashModInstr 7

private def muladdrshiftcHashModSetGasExact : Int :=
  computeExactGasBudget muladdrshiftcHashModGasProbeInstr

private def muladdrshiftcHashModSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne muladdrshiftcHashModGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tinyShiftPool : Array Nat :=
  #[1, 2, 3, 4, 5, 6, 7, 8]

private def tieShift1Pool : Array Int :=
  #[-15, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11, 13, 15]

private def tieShift2Pool : Array Int :=
  #[-14, -10, -6, -2, 2, 6, 10, 14]

private def smallSignedPool : Array Int :=
  #[-33, -17, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 17, 33]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (index, rng') := randNat rng 0 (pool.size - 1)
  (pool[index]!, rng')

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

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def pickOutOfRange (rng : StdGen) : Int × StdGen :=
  pickInt257OutOfRange rng

private def classifyMuladdrshiftcHashMod (left right addend : Int) (shift : Nat) : String :=
  let tmp : Int := left * right + addend
  let quotient := rshiftPow2Round tmp shift 1
  let remainder := modPow2Round tmp shift 1
  if !intFitsSigned257 quotient || !intFitsSigned257 remainder then
    "overflow"
  else if tmp = 0 then
    "zero"
  else if remainder = 0 then
    "exact"
  else if shift = 0 then
    "shift0"
  else
    let rawRemainder := Int.emod tmp (pow2 shift)
    if rawRemainder = pow2 (shift - 1) then
      "tie"
    else
      "inexact"

private def genMuladdrshiftcHashModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 33
  let (case0, rng2) :=
    if shape = 0 then
      let (left, rng2) := pickInt257Boundary rng1
      let (right, rng3) := pickInt257Boundary rng2
      let (addend, rng4) := pickInt257Boundary rng3
      let (shift, rng5) := pickShiftBoundary rng4
      let kind := classifyMuladdrshiftcHashMod left right addend shift
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/boundary-boundary-boundary-shift-boundary"
        shift #[intV left, intV right, intV addend], rng5)
    else if shape = 1 then
      let (left, rng2) := pickSigned257ish rng1
      let (right, rng3) := pickSigned257ish rng2
      let (addend, rng4) := pickSigned257ish rng3
      let (shift, rng5) := pickShiftBoundary rng4
      let kind := classifyMuladdrshiftcHashMod left right addend shift
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/random-random-random-shift-boundary"
        shift #[intV left, intV right, intV addend], rng5)
    else if shape = 2 then
      let (left, rng2) := pickInt257Boundary rng1
      let (right, rng3) := pickSigned257ish rng2
      let (addend, rng4) := pickSigned257ish rng3
      let (shift, rng5) := pickShiftMixed rng4
      let kind := classifyMuladdrshiftcHashMod left right addend shift
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/boundary-random-random-shift-random"
        shift #[intV left, intV right, intV addend], rng5)
    else if shape = 3 then
      let (left, rng2) := pickSigned257ish rng1
      let (right, rng3) := pickInt257Boundary rng2
      let (addend, rng4) := pickSigned257ish rng3
      let (shift, rng5) := pickShiftMixed rng4
      let kind := classifyMuladdrshiftcHashMod left right addend shift
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/random-boundary-random-shift-random"
        shift #[intV left, intV right, intV addend], rng5)
    else if shape = 4 then
      let (left, rng2) := pickSigned257ish rng1
      let (right, rng3) := pickSigned257ish rng2
      let (addend, rng4) := pickInt257Boundary rng3
      let (shift, rng5) := pickShiftMixed rng4
      let kind := classifyMuladdrshiftcHashMod left right addend shift
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/random-random-boundary-shift-random"
        shift #[intV left, intV right, intV addend], rng5)
    else if shape = 5 then
      let (tmpSeed, rng2) := pickFromPool tieShift1Pool rng1
      let kind := classifyMuladdrshiftcHashMod tmpSeed 1 0 1
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/tie-shift1"
        1 #[intV tmpSeed, intV 1, intV 0], rng2)
    else if shape = 6 then
      let (tmpSeed, rng2) := pickFromPool tieShift2Pool rng1
      let kind := classifyMuladdrshiftcHashMod tmpSeed 1 0 2
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/tie-shift2"
        2 #[intV tmpSeed, intV 1, intV 0], rng2)
    else if shape = 7 then
      let (right, rng2) := pickSigned257ish rng1
      let (addend, rng3) := pickSigned257ish rng2
      let (shift, rng4) := pickShiftMixed rng3
      let kind := classifyMuladdrshiftcHashMod 0 right addend shift
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/zero-left"
        shift #[intV 0, intV right, intV addend], rng4)
    else if shape = 8 then
      let (left, rng2) := pickSigned257ish rng1
      let (addend, rng3) := pickSigned257ish rng2
      let (shift, rng4) := pickShiftMixed rng3
      let kind := classifyMuladdrshiftcHashMod left 0 addend shift
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/zero-right"
        shift #[intV left, intV 0, intV addend], rng4)
    else if shape = 9 then
      let (left, rng2) := pickSigned257ish rng1
      let (right, rng3) := pickSigned257ish rng2
      let (shift, rng4) := pickShiftMixed rng3
      let kind := classifyMuladdrshiftcHashMod left right 0 shift
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/zero-addend"
        shift #[intV left, intV right, intV 0], rng4)
    else if shape = 10 then
      let (left, rng2) := pickSigned257ish rng1
      let (right, rng3) := pickSigned257ish rng2
      let (addend, rng4) := pickSigned257ish rng3
      let (shift, rng5) := pickShiftBoundary rng4
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/pop-order/lower-null-preserved"
        shift #[.null, intV left, intV right, intV addend], rng5)
    else if shape = 11 then
      let (left, rng2) := pickSigned257ish rng1
      let (right, rng3) := pickSigned257ish rng2
      let (addend, rng4) := pickSigned257ish rng3
      let (shift, rng5) := pickShiftBoundary rng4
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/pop-order/lower-cell-preserved"
        shift #[.cell Cell.empty, intV left, intV right, intV addend], rng5)
    else if shape = 12 then
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty-stack" 1 #[], rng1)
    else if shape = 13 then
      let (left, rng2) := pickSigned257ish rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/one-item" 1 #[intV left], rng2)
    else if shape = 14 then
      let (left, rng2) := pickSigned257ish rng1
      let (right, rng3) := pickSigned257ish rng2
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/two-items" 1 #[intV left, intV right], rng3)
    else if shape = 15 then
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type-two-non-int"
        1 #[.null, .cell Cell.empty], rng1)
    else if shape = 16 then
      let (left, rng2) := pickSigned257ish rng1
      let (right, rng3) := pickSigned257ish rng2
      let (shift, rng4) := pickShiftMixed rng3
      let (badAddend, rng5) := pickNonInt rng4
      (mkShiftCase s!"/fuzz/shape-{shape}/type/w-top-non-int"
        shift #[intV left, intV right, badAddend], rng5)
    else if shape = 17 then
      let (left, rng2) := pickSigned257ish rng1
      let (addend, rng3) := pickSigned257ish rng2
      let (shift, rng4) := pickShiftMixed rng3
      let (badRight, rng5) := pickNonInt rng4
      (mkShiftCase s!"/fuzz/shape-{shape}/type/y-second-non-int"
        shift #[intV left, badRight, intV addend], rng5)
    else if shape = 18 then
      let (right, rng2) := pickSigned257ish rng1
      let (addend, rng3) := pickSigned257ish rng2
      let (shift, rng4) := pickShiftMixed rng3
      let (badLeft, rng5) := pickNonInt rng4
      (mkShiftCase s!"/fuzz/shape-{shape}/type/x-third-non-int"
        shift #[badLeft, intV right, intV addend], rng5)
    else if shape = 19 then
      let (left, rng2) := pickSigned257ish rng1
      let (shift, rng3) := pickShiftMixed rng2
      let (badRight, rng4) := pickNonInt rng3
      let (badAddend, rng5) := pickNonInt rng4
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/pop-w-before-y-when-both-non-int"
        shift #[intV left, badRight, badAddend], rng5)
    else if shape = 20 then
      (mkShiftCase s!"/fuzz/shape-{shape}/intov/overflow-max-max-plus-max-shift1"
        1 #[intV maxInt257, intV maxInt257, intV maxInt257], rng1)
    else if shape = 21 then
      (mkShiftCase s!"/fuzz/shape-{shape}/intov/overflow-min-min-plus-min-shift1"
        1 #[intV minInt257, intV minInt257, intV minInt257], rng1)
    else if shape = 22 then
      (mkShiftCase s!"/fuzz/shape-{shape}/intov/overflow-max-min-plus-zero-shift1"
        1 #[intV maxInt257, intV minInt257, intV 0], rng1)
    else if shape = 23 then
      let (right, rng2) := pickSigned257ish rng1
      let (addend, rng3) := pickSigned257ish rng2
      let (shift, rng4) := pickShiftBoundary rng3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-nan-x-via-prelude"
        shift #[.nan, .num right, .num addend], rng4)
    else if shape = 24 then
      let (left, rng2) := pickSigned257ish rng1
      let (addend, rng3) := pickSigned257ish rng2
      let (shift, rng4) := pickShiftBoundary rng3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-nan-y-via-prelude"
        shift #[.num left, .nan, .num addend], rng4)
    else if shape = 25 then
      let (left, rng2) := pickSigned257ish rng1
      let (right, rng3) := pickSigned257ish rng2
      let (shift, rng4) := pickShiftBoundary rng3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-nan-w-via-prelude"
        shift #[.num left, .num right, .nan], rng4)
    else if shape = 26 then
      let (leftOutOfRange, rng2) := pickOutOfRange rng1
      let (right, rng3) := pickSigned257ish rng2
      let (addend, rng4) := pickSigned257ish rng3
      let (shift, rng5) := pickShiftBoundary rng4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-via-prelude"
        shift #[.num leftOutOfRange, .num right, .num addend], rng5)
    else if shape = 27 then
      let (left, rng2) := pickSigned257ish rng1
      let (rightOutOfRange, rng3) := pickOutOfRange rng2
      let (addend, rng4) := pickSigned257ish rng3
      let (shift, rng5) := pickShiftBoundary rng4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-via-prelude"
        shift #[.num left, .num rightOutOfRange, .num addend], rng5)
    else if shape = 28 then
      let (left, rng2) := pickSigned257ish rng1
      let (right, rng3) := pickSigned257ish rng2
      let (addendOutOfRange, rng4) := pickOutOfRange rng3
      let (shift, rng5) := pickShiftBoundary rng4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-via-prelude"
        shift #[.num left, .num right, .num addendOutOfRange], rng5)
    else if shape = 29 then
      let (useMaxLeft, rng2) := randBool rng1
      let (useNegativeRight, rng3) := randBool rng2
      let (useNegativeAddend, rng4) := randBool rng3
      let left : Int := if useMaxLeft then maxInt257 else minInt257
      let right : Int := if useNegativeRight then -1 else 1
      let addend : Int := if useNegativeAddend then -1 else 1
      let kind := classifyMuladdrshiftcHashMod left right addend 256
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/extreme-factor-shift256"
        256 #[intV left, intV right, intV addend], rng4)
    else if shape = 30 then
      let (left, rng2) := pickSigned257ish rng1
      let (right, rng3) := pickSigned257ish rng2
      let (addend, rng4) := pickSigned257ish rng3
      let kind := classifyMuladdrshiftcHashMod left right addend 1
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/random-sign-variation-shift1"
        1 #[intV left, intV right, intV addend], rng4)
    else if shape = 31 then
      let (quotientSeed, rng2) := pickFromPool smallSignedPool rng1
      let (shift, rng3) := pickFromPool tinyShiftPool rng2
      let left : Int := quotientSeed * intPow2 shift
      let kind := classifyMuladdrshiftcHashMod left 1 0 shift
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/constructed-divisible"
        shift #[intV left, intV 1, intV 0], rng3)
    else if shape = 32 then
      let (left, rng2) := pickFromPool smallSignedPool rng1
      let (right, rng3) := pickFromPool smallSignedPool rng2
      let (addend, rng4) := pickFromPool smallSignedPool rng3
      let (shift, rng5) := pickShiftMixed rng4
      let kind := classifyMuladdrshiftcHashMod left right addend shift
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/{kind}/small-signed"
        shift #[intV left, intV right, intV addend], rng5)
    else if shape = 33 then
      let (shift, rng2) := pickShiftBoundary rng1
      let (belowLike, rng3) := pickNonInt rng2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-with-below-via-prelude"
        shift #[.nan, .num 7, .num 3] #[belowLike], rng3)
    else
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/fallback" 1 #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := muladdrshiftcHashModId
  unit := #[
    { name := "/unit/direct/ceiling-rounding-sign-ties-and-output-order"
      run := do
        let checks : Array (Int × Int × Int × Nat) :=
          #[
            (7, 3, 1, 1),
            (7, 3, 0, 1),
            (-7, 3, 0, 1),
            (7, -3, 0, 1),
            (-7, -3, 0, 1),
            (5, 5, 0, 1),
            (-5, 5, 0, 1),
            (5, -5, 0, 1),
            (-5, -5, 0, 1),
            (42, 6, 3, 3),
            (-42, 6, 3, 3),
            (42, -6, 3, 3),
            (-42, -6, 3, 3),
            (1, 1, 0, 1),
            (-1, 1, 0, 1),
            (0, 9, 0, 7)
          ]
        for check in checks do
          let (left, right, addend, shift) := check
          let tmp := left * right + addend
          let quotient := rshiftPow2Round tmp shift 1
          let remainder := modPow2Round tmp shift 1
          expectOkStack s!"/unit/ok/left={left}/right={right}/addend={addend}/z={shift}"
            (runMuladdrshiftcHashModDirect shift #[intV left, intV right, intV addend])
            #[intV quotient, intV remainder] }
    ,
    { name := "/unit/direct/boundary-shift256-and-pop-order"
      run := do
        let checks : Array (Int × Int × Int × Nat) :=
          #[
            (maxInt257, 1, 0, 1),
            (minInt257, 1, 0, 1),
            (maxInt257, 1, 0, 256),
            (minInt257, 1, 0, 256),
            (maxInt257, 1, -1, 256),
            (minInt257, 1, 1, 256),
            (maxInt257, maxInt257, 0, 256),
            (maxInt257, 0, maxInt257, 256),
            (minInt257, 0, minInt257, 256),
            (maxInt257, -1, -1, 256)
          ]
        for check in checks do
          let (left, right, addend, shift) := check
          let tmp := left * right + addend
          let quotient := rshiftPow2Round tmp shift 1
          let remainder := modPow2Round tmp shift 1
          expectOkStack s!"/unit/boundary/left={left}/right={right}/addend={addend}/z={shift}"
            (runMuladdrshiftcHashModDirect shift #[intV left, intV right, intV addend])
            #[intV quotient, intV remainder]
        let popTmp1 := 7 * 3 + 0
        expectOkStack "/unit/pop-order/lower-null-preserved"
          (runMuladdrshiftcHashModDirect 1 #[.null, intV 7, intV 3, intV 0])
          #[.null, intV (rshiftPow2Round popTmp1 1 1), intV (modPow2Round popTmp1 1 1)]
        let popTmp2 := (-7) * 3 + 0
        expectOkStack "/unit/pop-order/lower-cell-preserved"
          (runMuladdrshiftcHashModDirect 1 #[.cell Cell.empty, intV (-7), intV 3, intV 0])
          #[.cell Cell.empty, intV (rshiftPow2Round popTmp2 1 1), intV (modPow2Round popTmp2 1 1)] }
    ,
    { name := "/unit/error/underflow-type-and-pop-order"
      run := do
        expectErr "/unit/error/underflow/empty"
          (runMuladdrshiftcHashModDirect 1 #[]) .stkUnd
        expectErr "/unit/error/underflow/one-item"
          (runMuladdrshiftcHashModDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow/two-items"
          (runMuladdrshiftcHashModDirect 1 #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-two-non-int"
          (runMuladdrshiftcHashModDirect 1 #[.null, .cell Cell.empty]) .stkUnd
        expectErr "/unit/error/type/w-top-null"
          (runMuladdrshiftcHashModDirect 1 #[intV 1, intV 2, .null]) .typeChk
        expectErr "/unit/error/type/w-top-cell"
          (runMuladdrshiftcHashModDirect 1 #[intV 1, intV 2, .cell Cell.empty]) .typeChk
        expectErr "/unit/error/type/y-second-null"
          (runMuladdrshiftcHashModDirect 1 #[intV 1, .null, intV 3]) .typeChk
        expectErr "/unit/error/type/x-third-null"
          (runMuladdrshiftcHashModDirect 1 #[.null, intV 2, intV 3]) .typeChk
        expectErr "/unit/error-order/pop-w-before-y-when-both-non-int"
          (runMuladdrshiftcHashModDirect 1 #[intV 1, .cell Cell.empty, .null]) .typeChk }
    ,
    { name := "/unit/error/intov-from-overflow"
      run := do
        expectErr "/unit/intov/overflow-max-max-plus-max-shift1"
          (runMuladdrshiftcHashModDirect 1 #[intV maxInt257, intV maxInt257, intV maxInt257]) .intOv
        expectErr "/unit/intov/overflow-min-min-plus-min-shift1"
          (runMuladdrshiftcHashModDirect 1 #[intV minInt257, intV minInt257, intV minInt257]) .intOv
        expectErr "/unit/intov/overflow-max-min-plus-zero-shift1"
          (runMuladdrshiftcHashModDirect 1 #[intV maxInt257, intV minInt257, intV 0]) .intOv
        expectErr "/unit/intov/overflow-max-max-plus-zero-shift1"
          (runMuladdrshiftcHashModDirect 1 #[intV maxInt257, intV maxInt257, intV 0]) .intOv }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instrShift1 := mkMuladdrshiftcHashModInstr 1
        let instrShift256 := mkMuladdrshiftcHashModInstr 256
        let program : Array Instr := #[instrShift1, instrShift256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error err => throw (IO.userError s!"/unit/opcode/assemble failed: {err}")
        let slice0 := Slice.ofCell code
        let slice1 ← expectDecodeStep "/unit/opcode/decode-z1" slice0 instrShift1 24
        let slice2 ← expectDecodeStep "/unit/opcode/decode-z256" slice1 instrShift256 24
        let slice3 ← expectDecodeStep "/unit/opcode/decode-tail-add" slice2 .add 8
        if slice3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/opcode/decode-end: expected exhausted slice, got {slice3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/opcode/encode-invalid-immediate-range"
      run := do
        let invalidLow := mkMuladdrshiftcHashModInstr 0
        let invalidHigh := mkMuladdrshiftcHashModInstr 257
        match assembleCp0 [invalidLow] with
        | .ok _ =>
            throw (IO.userError "/unit/opcode/encode-z0: expected rangeChk, got ok")
        | .error err =>
            if err = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"/unit/opcode/encode-z0: expected rangeChk, got {err}")
        match assembleCp0 [invalidHigh] with
        | .ok _ =>
            throw (IO.userError "/unit/opcode/encode-z257: expected rangeChk, got ok")
        | .error err =>
            if err = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"/unit/opcode/encode-z257: expected rangeChk, got {err}") }
    ,
    { name := "/unit/dispatch/non-muladdrshiftc-hash-mod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runMuladdrshiftcHashModDispatchFallback #[]) #[intV 9419] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/round/sign/pos-pos-shift1" 1 #[.num 7, .num 3, .num 0],
    mkShiftInputCase "/ok/round/sign/neg-pos-shift1" 1 #[.num (-7), .num 3, .num 0],
    mkShiftInputCase "/ok/round/sign/pos-neg-shift1" 1 #[.num 7, .num (-3), .num 0],
    mkShiftInputCase "/ok/round/sign/neg-neg-shift1" 1 #[.num (-7), .num (-3), .num 0],
    mkShiftInputCase "/ok/round/tie/plus-half" 1 #[.num 1, .num 1, .num 0],
    mkShiftInputCase "/ok/round/tie/minus-half-to-plus-inf" 1 #[.num (-1), .num 1, .num 0],
    mkShiftInputCase "/ok/round/tie/plus-three-halves" 1 #[.num 3, .num 1, .num 0],
    mkShiftInputCase "/ok/round/tie/minus-three-halves" 1 #[.num (-3), .num 1, .num 0],
    mkShiftInputCase "/ok/exact/divisible-shift1" 1 #[.num 21, .num 1, .num 11],
    mkShiftInputCase "/ok/exact/divisible-shift2-neg" 2 #[.num (-21), .num 1, .num 5],
    mkShiftInputCase "/ok/exact/divisible-shift3" 3 #[.num 40, .num 24, .num 8],
    mkShiftInputCase "/ok/nonexact/zero-left" 9 #[.num 0, .num 7, .num 11],
    mkShiftInputCase "/ok/nonexact/zero-right" 9 #[.num 7, .num 0, .num 11],
    mkShiftInputCase "/ok/boundary/max-times-one-shift1" 1 #[.num maxInt257, .num 1, .num 0],
    mkShiftInputCase "/ok/boundary/min-times-one-shift1" 1 #[.num minInt257, .num 1, .num 0],
    mkShiftInputCase "/ok/boundary/max-times-one-shift256" 256 #[.num maxInt257, .num 1, .num 0],
    mkShiftInputCase "/ok/boundary/min-times-one-shift256" 256 #[.num minInt257, .num 1, .num 0],
    mkShiftInputCase "/ok/boundary/max-times-one-minus-one-shift256"
      256 #[.num maxInt257, .num 1, .num (-1)],
    mkShiftInputCase "/ok/boundary/min-times-one-plus-one-shift256"
      256 #[.num minInt257, .num 1, .num 1],
    mkShiftInputCase "/ok/boundary/max-times-max-shift256"
      256 #[.num maxInt257, .num maxInt257, .num 0],
    mkShiftInputCase "/ok/boundary/w-dominates-shift256"
      256 #[.num maxInt257, .num 0, .num maxInt257],
    mkShiftCase "/ok/pop-order/lower-null-preserved" 1 #[.null, intV 7, intV 3, intV 0],
    mkShiftCase "/ok/pop-order/lower-cell-preserved" 1 #[.cell Cell.empty, intV (-7), intV 3, intV 0],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/underflow/one-item" 1 #[intV 1],
    mkShiftCase "/underflow/two-items" 1 #[intV 1, intV 2],
    mkShiftCase "/error-order/underflow-before-type-two-non-int" 1 #[.null, .cell Cell.empty],
    mkShiftCase "/type/w-top-null" 1 #[intV 1, intV 2, .null],
    mkShiftCase "/type/w-top-cell" 1 #[intV 1, intV 2, .cell Cell.empty],
    mkShiftCase "/type/y-second-null" 1 #[intV 1, .null, intV 3],
    mkShiftCase "/type/x-third-null" 1 #[.null, intV 2, intV 3],
    mkShiftCase "/error-order/pop-w-before-y-when-both-non-int"
      1 #[intV 1, .cell Cell.empty, .null],
    mkShiftCase "/intov/overflow-max-max-plus-max-shift1"
      1 #[intV maxInt257, intV maxInt257, intV maxInt257],
    mkShiftCase "/intov/overflow-min-min-plus-min-shift1"
      1 #[intV minInt257, intV minInt257, intV minInt257],
    mkShiftCase "/intov/overflow-max-min-plus-zero-shift1"
      1 #[intV maxInt257, intV minInt257, intV 0],
    mkShiftInputCase "/intov/nan-x-via-prelude"
      1 #[.nan, .num 7, .num 3],
    mkShiftInputCase "/intov/nan-y-via-prelude"
      1 #[.num 7, .nan, .num 3],
    mkShiftInputCase "/intov/nan-w-via-prelude"
      1 #[.num 7, .num 3, .nan],
    mkShiftInputCase "/intov/nan-all-via-prelude"
      1 #[.nan, .nan, .nan],
    mkShiftInputCase "/error-order/pushint-overflow-x-high-before-op"
      1 #[.num (maxInt257 + 1), .num 7, .num 3],
    mkShiftInputCase "/error-order/pushint-overflow-x-low-before-op"
      1 #[.num (minInt257 - 1), .num 7, .num 3],
    mkShiftInputCase "/error-order/pushint-overflow-y-high-before-op"
      1 #[.num 7, .num (maxInt257 + 1), .num 3],
    mkShiftInputCase "/error-order/pushint-overflow-y-low-before-op"
      1 #[.num 7, .num (minInt257 - 1), .num 3],
    mkShiftInputCase "/error-order/pushint-overflow-w-high-before-op"
      1 #[.num 7, .num 3, .num (maxInt257 + 1)],
    mkShiftInputCase "/error-order/pushint-overflow-w-low-before-op"
      1 #[.num 7, .num 3, .num (minInt257 - 1)],
    mkShiftInputCase "/error-order/pushint-overflow-multiple-before-op"
      1 #[.num (pow2 257), .num (-(pow2 257)), .num (maxInt257 + 2)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num muladdrshiftcHashModSetGasExact), .tonEnvOp .setGasLimit, muladdrshiftcHashModGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num muladdrshiftcHashModSetGasExactMinusOne), .tonEnvOp .setGasLimit, muladdrshiftcHashModGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020901
      count := 700
      gen := genMuladdrshiftcHashModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULADDRSHIFTC_HASH_MOD
