import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULMODPOW2R_HASH

/-
MULMODPOW2R# branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulShrModConst.lean`
    (`execInstrArithMulShrModConst`, `.mulShrModConst 2 0 z`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`modPow2Round`, nearest remainder behavior with ties toward `+∞`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (24-bit decode path `p12 = 0xa9b` for `MUL{RSHIFT,MODPOW2,RSHIFTMOD}#`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (hash-immediate `.mulShrModConst` encode routing for `0xa9b` family)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, hash-immediate mul-shr/mod family in `register_div_ops`)

Branch/terminal counts used for this suite specialization
(`d=2`, `roundMode=0`, hash-immediate `z ∈ [1, 256]`, non-quiet):
- Lean specialization: 5 branch sites / 7 terminal outcomes
  (dispatch/fallback; `y` pop underflow/type; `x` pop underflow/type;
   finite-vs-invalid operand split; non-quiet push success-vs-`intOv`).
- C++ specialization: 5 branch sites / 7 aligned terminal outcomes
  (opcode route; stack underflow/type on `y` then `x`; finite-vs-invalid split;
   non-quiet remainder push success-vs-`int_ov`).

Key risk areas covered:
- nearest-rounding remainder tie behavior after multiply (`roundMode = R`);
- strict pop/error ordering (`y` first, then `x`) including one-item edge cases;
- hash-immediate semantics: no runtime shift pop, lower stack preservation;
- NaN/out-of-range coverage only through `PUSHINT` prelude in oracle/fuzz inputs;
- exact gas boundary oracles via `computeExactGasBudget` helpers.
-/

private def mulModPow2RHashId : InstrId := { name := "MULMODPOW2R#" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkMulModPow2RHashInstr (shift : Nat) : Instr :=
  .mulShrModConst 2 0 shift

private def mulModPow2RHashOracleProxyInstr : Instr :=
  .arithExt (.shrMod true false 2 0 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulModPow2RHashOracleProxyInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := mulModPow2RHashId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkProxyInputCase
    (name : String)
    (x y shift : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[x, y, shift]
  mkCase name (below ++ stack) (progPrefix.push mulModPow2RHashOracleProxyInstr) gasLimits fuel

private def runMulModPow2RHashDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulShrModConst (mkMulModPow2RHashInstr shift) stack

private def runMulModPow2RHashDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulShrModConst .add (VM.push (intV 4971)) stack

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

private def mulModPow2RHashWord24 (shift : Nat) : Nat :=
  let cfg4 : Nat := (2 <<< 2) + 1
  (0xa9b <<< 12) + (cfg4 <<< 8) + (shift - 1)

private def mulModPow2RHashSetGasExact : Int :=
  computeExactGasBudget mulModPow2RHashOracleProxyInstr

private def mulModPow2RHashSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulModPow2RHashOracleProxyInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieFactorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def smallSignedPool : Array Int :=
  #[-21, -17, -13, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 13, 17, 21]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickFromNatPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromNatPool shiftBoundaryPool rng

private def pickShiftInRange (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 1 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  (if pickCell then .cell Cell.empty else .null, rng')

private def classifyMulModPow2R (x y : Int) (shift : Nat) : String :=
  let r := modPow2Round (x * y) shift 0
  if r = 0 then
    "ok-exact"
  else if shift > 0 ∧ Int.natAbs r = Int.natAbs (intPow2 (shift - 1)) then
    "ok-tie"
  else
    "ok-inexact"

private def genMulModPow2RHashFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyMulModPow2R x y shift
      (mkProxyInputCase s!"/fuzz/shape-{shape}/{kind}/boundary-triplet"
        (.num x) (.num y) (.num (Int.ofNat shift)), r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyMulModPow2R x y shift
      (mkProxyInputCase s!"/fuzz/shape-{shape}/{kind}/signed-triplet"
        (.num x) (.num y) (.num (Int.ofNat shift)), r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyMulModPow2R x y shift
      (mkProxyInputCase s!"/fuzz/shape-{shape}/{kind}/x-boundary"
        (.num x) (.num y) (.num (Int.ofNat shift)), r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyMulModPow2R x y shift
      (mkProxyInputCase s!"/fuzz/shape-{shape}/{kind}/y-boundary"
        (.num x) (.num y) (.num (Int.ofNat shift)), r4)
    else if shape = 4 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyMulModPow2R 0 y shift
      (mkProxyInputCase s!"/fuzz/shape-{shape}/{kind}/x-zero"
        (.num 0) (.num y) (.num (Int.ofNat shift)), r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyMulModPow2R x 0 shift
      (mkProxyInputCase s!"/fuzz/shape-{shape}/{kind}/y-zero"
        (.num x) (.num 0) (.num (Int.ofNat shift)), r3)
    else if shape = 6 then
      let (x, r2) := pickFromIntPool tieFactorPool rng1
      let (y, r3) := pickFromIntPool tieFactorPool r2
      (mkProxyInputCase s!"/fuzz/shape-{shape}/ok-tie/shift1"
        (.num x) (.num y) (.num 1), r3)
    else if shape = 7 then
      let (x, r2) := pickFromIntPool tieFactorPool rng1
      (mkProxyInputCase s!"/fuzz/shape-{shape}/ok-tie/shift2"
        (.num x) (.num 2) (.num 2), r2)
    else if shape = 8 then
      let (x, r2) := pickInt257Boundary rng1
      let (useNeg, r3) := randBool r2
      let y : Int := if useNeg then -1 else 1
      let kind := classifyMulModPow2R x y 256
      (mkProxyInputCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift256"
        (.num x) (.num y) (.num 256), r3)
    else if shape = 9 then
      let (x, r2) := pickFromIntPool smallSignedPool rng1
      let (y, r3) := pickFromIntPool smallSignedPool r2
      let (shift, r4) := pickShiftInRange r3
      let (below, r5) := pickNonInt r4
      let kind := classifyMulModPow2R x y shift
      (mkProxyInputCase s!"/fuzz/shape-{shape}/{kind}/pop-order/below-preserved"
        (.num x) (.num y) (.num (Int.ofNat shift)) #[below], r5)
    else if shape = 10 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 12 then
      let (v, r2) := pickNonInt rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order/one-non-int-underflow-before-type" #[v], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/shift-top-non-int"
        #[intV x, intV y, shiftLike], r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/y-second-non-int"
        #[intV x, yLike, intV (Int.ofNat shift)], r4)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/x-third-non-int"
        #[xLike, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 16 then
      let (shift, r2) := pickShiftInRange rng1
      let (xLike, r3) := pickNonInt r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-when-both-non-int"
        #[xLike, yLike, intV (Int.ofNat shift)], r4)
    else if shape = 17 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkProxyInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program"
        .nan (.num y) (.num (Int.ofNat shift)), r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkProxyInputCase s!"/fuzz/shape-{shape}/intov/nan-y-via-program"
        (.num x) .nan (.num (Int.ofNat shift)), r3)
    else if shape = 19 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkProxyInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        (.num xOut) (.num y) (.num (Int.ofNat shift)), r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftInRange r3
      (mkProxyInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        (.num x) (.num yOut) (.num (Int.ofNat shift)), r4)
    else
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let (below, r5) := pickNonInt r4
      (mkProxyInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-with-below-non-int"
        (.num xOut) (.num y) (.num (Int.ofNat shift)) #[below], r5)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulModPow2RHashId
  unit := #[
    { name := "/unit/direct/nearest-remainder-rounding-sensitive"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (0, 0, 1, 0),
            (7, 5, 1, -1),
            (-7, 5, 1, -1),
            (7, -5, 1, -1),
            (-7, -5, 1, -1),
            (3, 2, 2, -2),
            (-3, 2, 2, -2),
            (3, -2, 2, -2),
            (5, 1, 3, -3),
            (-5, 1, 3, 3),
            (9, 1, 2, 1),
            (-9, 1, 2, -1)
          ]
        for c in checks do
          match c with
          | (x, y, shift, expected) =>
              expectOkStack s!"/unit/direct/x={x}/y={y}/z={shift}"
                (runMulModPow2RHashDirect shift #[intV x, intV y]) #[intV expected] }
    ,
    { name := "/unit/direct/boundary-and-lower-stack-preservation"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (maxInt257, 1, 256, -1),
            (maxInt257 - 1, 1, 256, -2),
            (minInt257, 1, 256, 0),
            (minInt257 + 1, 1, 256, 1),
            (maxInt257, -1, 256, 1),
            (minInt257, -1, 256, 0),
            (pow2 255, 1, 256, -(pow2 255)),
            (-(pow2 255), 1, 256, -(pow2 255))
          ]
        for c in checks do
          match c with
          | (x, y, shift, expected) =>
              expectOkStack s!"/unit/boundary/x={x}/y={y}/z={shift}"
                (runMulModPow2RHashDirect shift #[intV x, intV y]) #[intV expected]
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runMulModPow2RHashDirect 1 #[.null, intV 7, intV 5]) #[.null, intV (-1)]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runMulModPow2RHashDirect 2 #[.cell Cell.empty, intV (-3), intV 2])
          #[.cell Cell.empty, intV (-2)] }
    ,
    { name := "/unit/error/underflow-type-and-pop-order"
      run := do
        expectErr "/unit/error/underflow-empty"
          (runMulModPow2RHashDirect 1 #[]) .stkUnd
        expectErr "/unit/error/underflow-one-int"
          (runMulModPow2RHashDirect 1 #[intV 7]) .stkUnd
        expectErr "/unit/error/one-non-int-is-type-before-x-underflow"
          (runMulModPow2RHashDirect 1 #[.null]) .typeChk
        expectErr "/unit/error/type-pop-y-first-null"
          (runMulModPow2RHashDirect 1 #[intV 7, .null]) .typeChk
        expectErr "/unit/error/type-pop-y-first-cell"
          (runMulModPow2RHashDirect 1 #[intV 7, .cell Cell.empty]) .typeChk
        expectErr "/unit/error/type-pop-x-second-null"
          (runMulModPow2RHashDirect 1 #[.null, intV 7]) .typeChk
        expectErr "/unit/error/order-pop-y-before-x-when-both-non-int"
          (runMulModPow2RHashDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkMulModPow2RHashInstr 1
        let instr256 := mkMulModPow2RHashInstr 256
        let bits : BitString :=
          natToBits (mulModPow2RHashWord24 1) 24
            ++ natToBits (mulModPow2RHashWord24 256) 24
            ++ natToBits 0xa0 8
        let code : Cell := Cell.mkOrdinary bits #[]
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/opcode/decode/mulmodpow2r-hash-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/opcode/decode/mulmodpow2r-hash-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/opcode/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/opcode/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining")
        let badCfgWord : Nat := (0xa9b <<< 12) + (1 <<< 8)
        let badCfgCode : Cell := Cell.mkOrdinary (natToBits badCfgWord 24) #[]
        match decodeCp0WithBits (Slice.ofCell badCfgCode) with
        | .error .invOpcode =>
            pure ()
        | .error e =>
            throw (IO.userError s!"/unit/opcode/decode/bad-cfg: expected invOpcode, got {e}")
        | .ok (instr, bitsUsed, _) =>
            throw (IO.userError s!"/unit/opcode/decode/bad-cfg: expected failure, decoded {reprStr instr} ({bitsUsed} bits)") }
    ,
    { name := "/unit/dispatch/non-mulmodpow2r-hash-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runMulModPow2RHashDispatchFallback #[]) #[intV 4971] }
  ]
  oracle := #[
    mkProxyInputCase "/proxy/ok/round/sign/pos-pos-shift1" (.num 7) (.num 5) (.num 1),
    mkProxyInputCase "/proxy/ok/round/sign/neg-pos-shift1" (.num (-7)) (.num 5) (.num 1),
    mkProxyInputCase "/proxy/ok/round/sign/pos-neg-shift1" (.num 7) (.num (-5)) (.num 1),
    mkProxyInputCase "/proxy/ok/round/sign/neg-neg-shift1" (.num (-7)) (.num (-5)) (.num 1),
    mkProxyInputCase "/proxy/ok/round/tie/plus-half-shift2" (.num 3) (.num 2) (.num 2),
    mkProxyInputCase "/proxy/ok/round/tie/minus-half-shift2" (.num (-3)) (.num 2) (.num 2),
    mkProxyInputCase "/proxy/ok/round/general/pos-shift3" (.num 5) (.num 1) (.num 3),
    mkProxyInputCase "/proxy/ok/round/general/neg-shift3" (.num (-5)) (.num 1) (.num 3),
    mkProxyInputCase "/proxy/ok/round/general/pos-neg-shift3" (.num 5) (.num (-1)) (.num 3),
    mkProxyInputCase "/proxy/ok/boundary/max-times-one-shift256" (.num maxInt257) (.num 1) (.num 256),
    mkProxyInputCase "/proxy/ok/boundary/min-times-one-shift256" (.num minInt257) (.num 1) (.num 256),
    mkProxyInputCase "/proxy/ok/boundary/max-times-neg1-shift256" (.num maxInt257) (.num (-1)) (.num 256),
    mkProxyInputCase "/proxy/ok/boundary/min-plus-one-times-one-shift256"
      (.num (minInt257 + 1)) (.num 1) (.num 256),
    mkProxyInputCase "/proxy/ok/zero-factor/x-zero" (.num 0) (.num 17) (.num 128),
    mkProxyInputCase "/proxy/ok/zero-factor/y-zero" (.num 17) (.num 0) (.num 128),
    mkProxyInputCase "/proxy/ok/pop-order/below-null-preserved"
      (.num 7) (.num 5) (.num 1) #[.null],
    mkProxyInputCase "/proxy/ok/pop-order/below-cell-preserved"
      (.num (-7)) (.num 5) (.num 2) #[.cell Cell.empty],
    mkCase "/proxy/underflow/empty" #[],
    mkCase "/proxy/underflow/one-item-int" #[intV 7],
    mkCase "/proxy/error-order/one-item-non-int-underflow-before-type" #[.null],
    mkCase "/proxy/type/shift-top-non-int" #[intV 7, intV 5, .null],
    mkCase "/proxy/type/y-second-non-int" #[intV 7, .null, intV 2],
    mkCase "/proxy/type/x-third-non-int" #[.null, intV 5, intV 2],
    mkCase "/proxy/error-order/pop-y-before-x-when-both-non-int" #[.null, .cell Cell.empty, intV 2],
    mkProxyInputCase "/proxy/intov/nan-x-via-program" .nan (.num 5) (.num 2),
    mkProxyInputCase "/proxy/intov/nan-y-via-program" (.num 7) .nan (.num 2),
    mkProxyInputCase "/proxy/intov/nan-both-via-program" .nan .nan (.num 2),
    mkProxyInputCase "/proxy/error-order/pushint-overflow-x-high-before-op"
      (.num (maxInt257 + 1)) (.num 5) (.num 2),
    mkProxyInputCase "/proxy/error-order/pushint-overflow-x-low-before-op"
      (.num (minInt257 - 1)) (.num 5) (.num 2),
    mkProxyInputCase "/proxy/error-order/pushint-overflow-y-high-before-op"
      (.num 7) (.num (maxInt257 + 1)) (.num 2),
    mkProxyInputCase "/proxy/error-order/pushint-overflow-y-low-before-op"
      (.num 7) (.num (minInt257 - 1)) (.num 2),
    mkProxyInputCase "/proxy/error-order/pushint-overflow-before-op-with-below-non-int"
      (.num (maxInt257 + 1)) (.num 7) (.num 2) #[.null],
    mkCase "/proxy/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulModPow2RHashSetGasExact), .tonEnvOp .setGasLimit, mulModPow2RHashOracleProxyInstr],
    mkCase "/proxy/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num mulModPow2RHashSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulModPow2RHashOracleProxyInstr]
  ]
  fuzz := #[
    { seed := 2026020898
      count := 700
      gen := genMulModPow2RHashFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULMODPOW2R_HASH
