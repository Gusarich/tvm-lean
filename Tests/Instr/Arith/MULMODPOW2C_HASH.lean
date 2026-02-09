import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULMODPOW2C_HASH

/-
MULMODPOW2C# branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulShrModConst.lean`
    (`execInstrArithMulShrModConst`, `.mulShrModConst 2 1 z`)
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, executable oracle model `.shrMod true false 2 1 false none`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`modPow2Round`, ceil-mod remainder semantics)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (24-bit hash decode family `0xa9b***` to `.mulShrModConst d roundMode z`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, const-shift decode route in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean hash executor (`execInstrArithMulShrModConst`, `d=2`, `round=+1`):
  7 branch sites / 10 terminal outcomes
  (dispatch/fallback; `y` pop underflow/type/success; `x` pop underflow/type/success;
   finite-vs-NaN split; `d` switch; non-quiet push success-vs-`intOv`).
- Lean executable oracle model (`PUSHINT z; MULMODPOW2C`):
  8 branch sites / 11 terminal outcomes
  (runtime shift injection success/failure; underflow/type gates for `y/x`;
   finite-vs-NaN split; ceil-mod data path; non-quiet push success-vs-`intOv`).
- Cp0 hash decode (`0xa9b` family):
  3 branch sites / 5 outcomes
  (prefix match; cfg unpack (`d`, `roundMode`); invalid cfg rejection vs success).
- C++ (`exec_mulshrmod`, const-shift + non-quiet):
  7 branch sites / 10 aligned outcomes
  (underflow/type order, finite-vs-invalid path, `d` switch, push overflow funnel).

Key risk areas covered:
- ceil-mod sign/tie behavior for `x*y mod 2^z` (`z ∈ [1, 256]`);
- hash-immediate pop-order (`y` then `x`) with lower-stack preservation;
- strict underflow/type ordering and `d`-switch invalid-op path;
- raw hash decode boundaries (`z=1`, `z=256`) and invalid cfg rejection;
- program-injected NaN / out-of-range values only through instruction prelude;
- exact gas cliff (`SETGASLIMIT` exact vs exact-minus-one) on executable oracle model.
-/

private def mulmodpow2cHashId : InstrId := { name := "MULMODPOW2C#" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkMulmodpow2cHashInstr (shift : Nat) : Instr :=
  .mulShrModConst 2 1 shift

/--
Executable oracle model for `MULMODPOW2C#`:
`PUSHINT z; MULMODPOW2C` with `z` fixed by program prelude.
-/
private def mulmodpow2cRuntimeInstr : Instr :=
  .arithExt (.shrMod true false 2 1 false none)

private def mkOracleModelProgram (shift : Nat) : Array Instr :=
  #[.pushInt (.num (Int.ofNat shift)), mulmodpow2cRuntimeInstr]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := mkOracleModelProgram 1)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := mulmodpow2cHashId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkShiftStackCase
    (name : String)
    (shift : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (mkOracleModelProgram shift) gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (progPrefix ++ mkOracleModelProgram shift) gasLimits fuel

private def runMulmodpow2cHashDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulShrModConst (mkMulmodpow2cHashInstr shift) stack

private def runMulmodpow2cHashOracleModel
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt mulmodpow2cRuntimeInstr (stack.push (intV (Int.ofNat shift)))

private def runMulmodpow2cHashDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulShrModConst .add (VM.push (intV 9673)) stack

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

private def expectDecodeErr
    (label : String)
    (s : Slice)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")

private def mkMulHashWord24 (cfg4 : Nat) (arg8 : Nat) : Nat :=
  (0xa9b <<< 12) + ((cfg4 &&& 0xf) <<< 8) + (arg8 &&& 0xff)

private def mkMulHashRawCell (cfg4 : Nat) (arg8 : Nat) : Cell :=
  Cell.mkOrdinary (natToBits (mkMulHashWord24 cfg4 arg8) 24) #[]

private def mkMulHashRawSequenceCell (arg8a arg8b : Nat) : Cell :=
  let bits :=
    natToBits (mkMulHashWord24 0xa arg8a) 24 ++
    natToBits (mkMulHashWord24 0xa arg8b) 24 ++
    natToBits 0xa0 8
  Cell.mkOrdinary bits #[]

private def gasForInstrWithFallback (instr : Instr) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok budget => budget
  | .error _ => instrGas instr 16

private def setGasNeedForOracleModel (shift : Nat) (n : Int) : Int :=
  gasForInstrWithFallback (.pushInt (.num n))
    + gasForInstrWithFallback (.tonEnvOp .setGasLimit)
    + gasForInstrWithFallback (.pushInt (.num (Int.ofNat shift)))
    + gasForInstrWithFallback mulmodpow2cRuntimeInstr
    + implicitRetGasPrice

private def exactGasBudgetOracleModelFixedPoint (shift : Nat) (n : Int) : Nat → Int
  | 0 => n
  | k + 1 =>
      let n' := setGasNeedForOracleModel shift n
      if n' = n then n else exactGasBudgetOracleModelFixedPoint shift n' k

private def computeExactGasBudgetOracleModel (shift : Nat) : Int :=
  exactGasBudgetOracleModelFixedPoint shift 96 16

private def computeExactGasBudgetOracleModelMinusOne (shift : Nat) : Int :=
  let budget := computeExactGasBudgetOracleModel shift
  if budget > 0 then budget - 1 else 0

private def mulmodpow2cHashGasProbeShift : Nat := 7

private def mulmodpow2cHashSetGasExact : Int :=
  computeExactGasBudgetOracleModel mulmodpow2cHashGasProbeShift

private def mulmodpow2cHashSetGasExactMinusOne : Int :=
  computeExactGasBudgetOracleModelMinusOne mulmodpow2cHashGasProbeShift

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def smallFactorPool : Array Int :=
  #[-7, -5, -3, -1, 0, 1, 3, 5, 7]

private def pickNatFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickIntFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickNatFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def classifyMulmodpow2cHash (x y : Int) (shift : Nat) : String :=
  let r := modPow2Round (x * y) shift 1
  if r = 0 then
    "ok-exact"
  else if shift = 256 then
    "ok-shift256"
  else if decide (x < 0 ∨ y < 0) then
    "ok-sign-mixed"
  else
    "ok-sign-pos"

private def genMulmodpow2cHashFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyMulmodpow2cHash x y shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/boundary-triplet"
        shift #[intV x, intV y], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyMulmodpow2cHash x y shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/signed-triplet"
        shift #[intV x, intV y], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickIntFromPool smallFactorPool r2
      let kind := classifyMulmodpow2cHash x y 256
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/shift256-boundary-x-small-y"
        256 #[intV x, intV y], r3)
    else if shape = 3 then
      let (x, r2) := pickIntFromPool smallFactorPool rng1
      let (y, r3) := pickIntFromPool smallFactorPool r2
      let (shift, r4) := pickNatFromPool #[1, 2, 3, 4] r3
      let kind := classifyMulmodpow2cHash x y shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/small-factor-sign-focus"
        shift #[intV x, intV y], r4)
    else if shape = 4 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/empty-stack" shift #[], r2)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/single-int" shift #[intV x], r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (yBad, r3) := pickNonInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/pop-y-first" shift #[intV x, yBad], r4)
    else if shape = 7 then
      let (xBad, r2) := pickNonInt rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/pop-x-second" shift #[xBad, intV y], r4)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (below, r4) := pickNonInt r3
      let (shift, r5) := pickShiftBoundary r4
      let kind := classifyMulmodpow2cHash x y shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/pop-order/lower-preserved"
        shift #[below, intV x, intV y], r5)
    else if shape = 9 then
      let (xBad, r2) := pickNonInt rng1
      let (yBad, r3) := pickNonInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-when-both-non-int"
        shift #[xBad, yBad], r4)
    else if shape = 10 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program"
        shift #[.nan, .num y], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-y-via-program"
        shift #[.num x, .nan], r3)
    else if shape = 12 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        shift #[.num xOut, .num y], r4)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        shift #[.num x, .num yOut], r4)
    else if shape = 14 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-prelude-before-op-type"
        #[.null, intV 3]
        (#[.pushInt (.num (pow2 257))] ++ mkOracleModelProgram shift), r2)
    else if shape = 15 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-prelude-before-op-underflow"
        #[]
        (#[.pushInt (.num (-(pow2 257)))] ++ mkOracleModelProgram shift), r2)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/ok-exact/zero-factor-right"
        shift #[intV x, intV 0], r3)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/ok-exact/zero-factor-left"
        shift #[intV 0, intV x], r3)
    else if shape = 18 then
      let (pickMin, r2) := randBool rng1
      let x : Int := if pickMin then minInt257 else maxInt257
      let (y, r3) := pickIntFromPool #[-1, 1] r2
      let kind := classifyMulmodpow2cHash x y 256
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/extreme-x-small-y-shift256"
        256 #[intV x, intV y], r3)
    else
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyMulmodpow2cHash x y shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/fallback-signed-triplet"
        shift #[intV x, intV y], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulmodpow2cHashId
  unit := #[
    { name := "/unit/direct/ceil-mod-sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (7, 3, 1, -1),
            (7, 3, 2, -3),
            (-7, 3, 1, -1),
            (-7, 3, 2, -1),
            (7, -3, 2, -1),
            (-7, -3, 2, -3),
            (1, 1, 1, -1),
            (-1, 1, 1, -1),
            (42, 2, 1, 0),
            (-42, 2, 1, 0),
            (5, 5, 3, -7),
            (-5, 5, 3, -1)
          ]
        for c in checks do
          match c with
          | (x, y, shift, expected) =>
              expectOkStack s!"/unit/direct/x={x}/y={y}/z={shift}"
                (runMulmodpow2cHashDirect shift #[intV x, intV y]) #[intV expected] }
    ,
    { name := "/unit/direct/boundary-shifts-and-pop-order"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (maxInt257, 1, 1, -1),
            (minInt257, 1, 1, 0),
            (maxInt257, 1, 256, -1),
            (maxInt257 - 1, 1, 256, -2),
            (minInt257, 1, 256, 0),
            (minInt257 + 1, 1, 256, minInt257 + 1),
            (1, 1, 256, minInt257 + 1),
            (-1, 1, 256, -1),
            (maxInt257, -1, 256, minInt257 + 1)
          ]
        for c in checks do
          match c with
          | (x, y, shift, expected) =>
              expectOkStack s!"/unit/boundary/x={x}/y={y}/z={shift}"
                (runMulmodpow2cHashDirect shift #[intV x, intV y]) #[intV expected]
        expectOkStack "/unit/pop-order/lower-null-preserved"
          (runMulmodpow2cHashDirect 1 #[.null, intV 7, intV 3]) #[.null, intV (-1)]
        expectOkStack "/unit/pop-order/lower-cell-preserved"
          (runMulmodpow2cHashDirect 256 #[.cell Cell.empty, intV (-1), intV 1])
          #[.cell Cell.empty, intV (-1)] }
    ,
    { name := "/unit/error/underflow-type-ordering-and-nan-paths"
      run := do
        expectErr "/unit/underflow/empty-stack"
          (runMulmodpow2cHashDirect 1 #[]) .stkUnd
        expectErr "/unit/underflow/single-int"
          (runMulmodpow2cHashDirect 1 #[intV 7]) .stkUnd
        expectErr "/unit/type/pop-y-first-null"
          (runMulmodpow2cHashDirect 1 #[intV 7, .null]) .typeChk
        expectErr "/unit/type/pop-x-second-null"
          (runMulmodpow2cHashDirect 1 #[.null, intV 7]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-when-both-non-int"
          (runMulmodpow2cHashDirect 1 #[.null, .cell Cell.empty]) .typeChk
        expectErr "/unit/intov/nan-x-direct"
          (runMulmodpow2cHashDirect 1 #[.int .nan, intV 7]) .intOv
        expectErr "/unit/intov/nan-y-direct"
          (runMulmodpow2cHashDirect 1 #[intV 7, .int .nan]) .intOv }
    ,
    { name := "/unit/direct/hash-vs-runtime-model-equivalence-sanity"
      run := do
        let checks : Array (Int × Int × Nat) :=
          #[
            (7, 3, 1),
            (7, 3, 2),
            (-7, 3, 2),
            (maxInt257, 1, 256),
            (minInt257 + 1, -1, 256),
            (0, 99, 7)
          ]
        for c in checks do
          match c with
          | (x, y, shift) =>
              let direct := runMulmodpow2cHashDirect shift #[intV x, intV y]
              let model := runMulmodpow2cHashOracleModel shift #[intV x, intV y]
              match direct, model with
              | .ok ds, .ok ms =>
                  if ds == ms then
                    pure ()
                  else
                    throw (IO.userError s!"/unit/equiv/x={x}/y={y}/z={shift}: direct={reprStr ds}, model={reprStr ms}")
              | .error de, .error me =>
                  if de == me then
                    pure ()
                  else
                    throw (IO.userError s!"/unit/equiv/x={x}/y={y}/z={shift}: directErr={de}, modelErr={me}")
              | _, _ =>
                  throw (IO.userError s!"/unit/equiv/x={x}/y={y}/z={shift}: direct={reprStr direct}, model={reprStr model}") }
    ,
    { name := "/unit/opcode/raw-decode-hash-immediate-sequence"
      run := do
        let instr1 := mkMulmodpow2cHashInstr 1
        let instr256 := mkMulmodpow2cHashInstr 256
        let s0 := Slice.ofCell (mkMulHashRawSequenceCell 0 255)
        let s1 ← expectDecodeStep "/unit/decode/mulmodpow2c-hash-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/mulmodpow2c-hash-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/opcode/decode-invalid-cfg"
      run := do
        let _ ← expectDecodeStep "/unit/decode/d-zero-routes-to-other-hash-op"
          (Slice.ofCell (mkMulHashRawCell 0x1 0))
          (.arithExt (.shrMod true true 3 0 false (some 1)))
          24
        expectDecodeErr "/unit/decode/invalid-roundmode-two"
          (Slice.ofCell (mkMulHashRawCell 0xb 0)) .invOpcode }
    ,
    { name := "/unit/error/invalid-d-dispatch-and-fallback"
      run := do
        expectErr "/unit/error/d-zero-invalid-opcode"
          (runHandlerDirect execInstrArithMulShrModConst (.mulShrModConst 0 1 1) #[intV 7, intV 3]) .invOpcode
        expectOkStack "/unit/dispatch/fallback"
          (runMulmodpow2cHashDispatchFallback #[]) #[intV 9673] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/ceil/sign/pos-pos-shift1" 1 #[.num 7, .num 3],
    mkShiftInputCase "/ok/ceil/sign/pos-pos-shift2" 2 #[.num 7, .num 3],
    mkShiftInputCase "/ok/ceil/sign/neg-pos-shift1" 1 #[.num (-7), .num 3],
    mkShiftInputCase "/ok/ceil/sign/neg-pos-shift2" 2 #[.num (-7), .num 3],
    mkShiftInputCase "/ok/ceil/sign/pos-neg-shift2" 2 #[.num 7, .num (-3)],
    mkShiftInputCase "/ok/ceil/sign/neg-neg-shift2" 2 #[.num (-7), .num (-3)],
    mkShiftInputCase "/ok/ceil/tie/pos-half-shift1" 1 #[.num 1, .num 1],
    mkShiftInputCase "/ok/ceil/tie/neg-half-shift1" 1 #[.num (-1), .num 1],
    mkShiftInputCase "/ok/ceil/exact/pos" 1 #[.num 42, .num 2],
    mkShiftInputCase "/ok/ceil/exact/neg" 1 #[.num (-42), .num 2],
    mkShiftInputCase "/ok/ceil/small-shift3-pos" 3 #[.num 5, .num 5],
    mkShiftInputCase "/ok/ceil/small-shift3-neg" 3 #[.num (-5), .num 5],
    mkShiftInputCase "/ok/boundary/max-shift256" 256 #[.num maxInt257, .num 1],
    mkShiftInputCase "/ok/boundary/max-minus-one-shift256" 256 #[.num (maxInt257 - 1), .num 1],
    mkShiftInputCase "/ok/boundary/min-shift256" 256 #[.num minInt257, .num 1],
    mkShiftInputCase "/ok/boundary/min-plus-one-shift256" 256 #[.num (minInt257 + 1), .num 1],
    mkShiftInputCase "/ok/boundary/one-shift256" 256 #[.num 1, .num 1],
    mkShiftInputCase "/ok/boundary/minus-one-shift256" 256 #[.num (-1), .num 1],
    mkShiftInputCase "/ok/boundary/max-times-negone-shift256" 256 #[.num maxInt257, .num (-1)],
    mkShiftStackCase "/ok/pop-order/lower-null-preserved" 1 #[.null, intV 7, intV 3],
    mkShiftStackCase "/ok/pop-order/lower-cell-preserved" 256 #[.cell Cell.empty, intV (-1), intV 1],
    mkShiftStackCase "/underflow/empty-stack" 1 #[],
    mkShiftStackCase "/underflow/single-int" 1 #[intV 7],
    mkShiftStackCase "/type/pop-y-first-null" 1 #[intV 7, .null],
    mkShiftStackCase "/type/pop-x-second-null" 1 #[.null, intV 7],
    mkShiftStackCase "/error-order/pop-y-before-x-when-both-non-int" 1 #[.null, .cell Cell.empty],
    mkShiftInputCase "/intov/nan-x-via-program" 1 #[.nan, .num 3],
    mkShiftInputCase "/intov/nan-y-via-program" 1 #[.num 7, .nan],
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op" 1 #[.num (maxInt257 + 1), .num 3],
    mkShiftInputCase "/error-order/pushint-overflow-y-before-op" 1 #[.num 7, .num (minInt257 - 1)],
    mkCase "/error-order/pushint-overflow-prelude-before-op-type"
      #[.null, intV 3]
      (#[.pushInt (.num (pow2 257))] ++ mkOracleModelProgram 1),
    mkCase "/error-order/pushint-overflow-prelude-before-op-underflow"
      #[]
      (#[.pushInt (.num (-(pow2 257)))] ++ mkOracleModelProgram 1),
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5]
      (#[.pushInt (.num mulmodpow2cHashSetGasExact), .tonEnvOp .setGasLimit] ++
        mkOracleModelProgram mulmodpow2cHashGasProbeShift),
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      (#[.pushInt (.num mulmodpow2cHashSetGasExactMinusOne), .tonEnvOp .setGasLimit] ++
        mkOracleModelProgram mulmodpow2cHashGasProbeShift)
  ]
  fuzz := #[
    { seed := 2026020907
      count := 700
      gen := genMulmodpow2cHashFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULMODPOW2C_HASH
