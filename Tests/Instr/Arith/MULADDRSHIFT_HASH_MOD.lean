import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULADDRSHIFT_HASH_MOD

/-
MULADDRSHIFT#MOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true true 3 (-1) false (some z)` specialization)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type/overflow behavior)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate MUL+ADD+SHR/MOD family `0xa9b0..0xa9b2`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, 24-bit hash-immediate decode path with `z = arg8 + 1`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, hash-immediate registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, non-quiet push path)

Branch/terminal counts used for this suite
(`mul=true`, `add=true`, `d=3`, `roundMode=-1`, `quiet=false`, `zOpt=some z`):
- Lean specialization: ~8 branch sites / ~11 terminal outcomes
  (dispatch/fallback; 3-arg underflow gate; immediate range gate; ordered pops `w→y→x`;
   numeric-vs-invalid split; floor q/r path; non-quiet dual-push overflow funnel).
- C++ specialization: ~8 branch sites / ~10 aligned terminal outcomes
  (`check_underflow(3)` for hash-immediate add path; immediate decode-range discipline;
   `w→y→x` pop order; invalid-input funnel; floor q/r path; non-quiet push overflow).

Key risk areas covered:
- hash-immediate discipline (`z` encoded by opcode, never popped from stack);
- floor quotient/remainder behavior for `(x*y + w) / 2^z`, including sign-mixed inputs;
- strict error precedence: underflow before range, and range before `w/y/x` type checks;
- pop ordering (`w` first, then `y`, then `x`) with lower-stack preservation;
- NaN/out-of-range oracle serialization hygiene via prelude injection only
  (`oracleIntInputsToStackOrProgram` + `PUSHINT` prefix);
- exact gas boundary (`PUSHINT n; SETGASLIMIT; MULADDRSHIFT#MOD`) exact vs minus-one.
-/

private def muladdrshiftHashModId : InstrId := { name := "MULADDRSHIFT#MOD" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkMuladdrshiftHashModInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod true true 3 (-1) false (some shift))

private def muladdrshiftHashModInstrDefault : Instr :=
  mkMuladdrshiftHashModInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[muladdrshiftHashModInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := muladdrshiftHashModId
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
  mkCase name stack #[mkMuladdrshiftHashModInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (x y w : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkMuladdrshiftHashModInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram #[x, y, w]
  mkCase name (below ++ stack) (progPrefix.push instr) gasLimits fuel

private def runMuladdrshiftHashModDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkMuladdrshiftHashModInstr shift) stack

private def runMuladdrshiftHashModDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 7461)) stack

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

private def muladdrshiftHashModGasProbeInstr : Instr :=
  mkMuladdrshiftHashModInstr 7

private def muladdrshiftHashModSetGasExact : Int :=
  computeExactGasBudget muladdrshiftHashModGasProbeInstr

private def muladdrshiftHashModSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne muladdrshiftHashModGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def smallSignedPool : Array Int :=
  #[-33, -17, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 17, 33]

private def tinySignedPool : Array Int :=
  #[-3, -2, -1, 0, 1, 2, 3]

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

private def pickSmallOperand (rng : StdGen) : Int × StdGen :=
  pickFromPool smallSignedPool rng

private def pickTinyOperand (rng : StdGen) : Int × StdGen :=
  pickFromPool tinySignedPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  (if pickCell then .cell Cell.empty else .null, rng')

private def classifyMuladdrshiftHashMod (x y w : Int) (shift : Nat) : String :=
  let tmp : Int := x * y + w
  let q := rshiftPow2Round tmp shift (-1)
  let r := modPow2Round tmp shift (-1)
  if !intFitsSigned257 q || !intFitsSigned257 r then
    "intov"
  else if tmp = 0 then
    "ok-zero"
  else if r = 0 then
    "ok-exact"
  else if tmp < 0 then
    "ok-inexact-neg"
  else
    "ok-inexact-pos"

private def mkFiniteFuzzCase (shape : Nat) (x y w : Int) (shift : Nat) : OracleCase :=
  let kind := classifyMuladdrshiftHashMod x y w shift
  mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}" shift (.num x) (.num y) (.num w)

private def genMuladdrshiftHashModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 35
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (w, r4) := pickInt257Boundary r3
      let (shift, r5) := pickShiftBoundary r4
      (mkFiniteFuzzCase shape x y w shift, r5)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftMixed r4
      (mkFiniteFuzzCase shape x y w shift, r5)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftMixed r4
      (mkFiniteFuzzCase shape x y w shift, r5)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickInt257Boundary r3
      let (shift, r5) := pickShiftMixed r4
      (mkFiniteFuzzCase shape x y w shift, r5)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftMixed r4
      (mkFiniteFuzzCase shape x y w shift, r5)
    else if shape = 5 then
      let (x, r2) := pickSmallOperand rng1
      let (y, r3) := pickSmallOperand r2
      let (w, r4) := pickSmallOperand r3
      let (shift, r5) := pickShiftBoundary r4
      (mkFiniteFuzzCase shape x y w shift, r5)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      (mkFiniteFuzzCase shape x 0 w shift, r4)
    else if shape = 7 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      (mkFiniteFuzzCase shape 0 y w shift, r4)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      (mkFiniteFuzzCase shape x y 0 shift, r4)
    else if shape = 9 then
      let (x, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickTinyOperand r2
      let y := if y0 = 0 then 1 else y0
      let (w, r4) := pickTinyOperand r3
      (mkFiniteFuzzCase shape x y w 256, r4)
    else if shape = 10 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/overflow-max-max-plus-max-shift1"
        1 (.num maxInt257) (.num maxInt257) (.num maxInt257), rng1)
    else if shape = 11 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/overflow-min-min-plus-min-shift1"
        1 (.num minInt257) (.num minInt257) (.num minInt257), rng1)
    else if shape = 12 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/overflow-min-min-plus-zero-shift256"
        256 (.num minInt257) (.num minInt257) (.num 0), rng1)
    else if shape = 13 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/empty-stack" shift #[], r2)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/one-int" shift #[intV x], r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/two-ints"
        shift #[intV x, intV y], r4)
    else if shape = 16 then
      let (a, r2) := pickNonInt rng1
      let (b, r3) := pickNonInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type-two-non-int"
        shift #[a, b], r4)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (badW, r4) := pickNonInt r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/pop-w-first"
        shift #[intV x, intV y, badW], r5)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (badY, r4) := pickNonInt r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/pop-y-second"
        shift #[intV x, badY, intV w], r5)
    else if shape = 19 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (badX, r4) := pickNonInt r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/pop-x-third"
        shift #[badX, intV y, intV w], r5)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (badY, r3) := pickNonInt r2
      let (badW, r4) := pickNonInt r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/pop-w-before-y-when-both-non-int"
        shift #[intV x, badY, badW], r5)
    else if shape = 21 then
      let (w, r2) := pickSigned257ish rng1
      let (badX, r3) := pickNonInt r2
      let (badY, r4) := pickNonInt r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-when-both-non-int"
        shift #[badX, badY, intV w], r5)
    else if shape = 22 then
      let (x, r2) := pickSmallOperand rng1
      let (y, r3) := pickSmallOperand r2
      let (w, r4) := pickSmallOperand r3
      let (below, r5) := pickNonInt r4
      let (shift, r6) := pickShiftBoundary r5
      (mkShiftStackCase s!"/fuzz/shape-{shape}/pop-order/lower-preserved"
        shift #[below, intV x, intV y, intV w], r6)
    else if shape = 23 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/range/immediate-overmax"
        257 #[intV x, intV y, intV w], r4)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/range-before-w-type"
        257 #[intV x, intV y, .null], r3)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/range-before-y-type"
        257 #[intV x, .null, intV w], r3)
    else if shape = 26 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/range-before-x-type"
        257 #[.null, intV y, intV w], r3)
    else if shape = 27 then
      let (y, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program"
        shift .nan (.num y) (.num w), r4)
    else if shape = 28 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-y-via-program"
        shift (.num x) .nan (.num w), r4)
    else if shape = 29 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-w-via-program"
        shift (.num x) (.num y) .nan, r4)
    else if shape = 30 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        shift (.num xo) (.num y) (.num w), r5)
    else if shape = 31 then
      let (x, r2) := pickSigned257ish rng1
      let (yo, r3) := pickInt257OutOfRange r2
      let (w, r4) := pickSigned257ish r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        shift (.num x) (.num yo) (.num w), r5)
    else if shape = 32 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (wo, r4) := pickInt257OutOfRange r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        shift (.num x) (.num y) (.num wo), r5)
    else if shape = 33 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (yo, r3) := pickInt257OutOfRange r2
      let (wo, r4) := pickInt257OutOfRange r3
      let (shift, r5) := pickShiftBoundary r4
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-all-before-op"
        shift (.num xo) (.num yo) (.num wo), r5)
    else if shape = 34 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-type-check"
        #[.null] #[.pushInt (.num (pow2 257)), mkMuladdrshiftHashModInstr shift], r2)
    else
      let (shift, r2) := pickShiftBoundary rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-underflow"
        #[] #[.pushInt (.num (-(pow2 257))), mkMuladdrshiftHashModInstr shift], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := muladdrshiftHashModId
  unit := #[
    { name := "/unit/direct/floor-quot-rem-sign-and-boundary-shifts"
      run := do
        let checks : Array (Int × Int × Int × Nat × Int × Int) :=
          #[
            (7, 3, 1, 1, 11, 0),
            (-7, 3, 1, 1, -10, 0),
            (7, -3, 1, 1, -10, 0),
            (-7, -3, 1, 1, 11, 0),
            (5, 5, -2, 2, 5, 3),
            (-5, 5, 2, 2, -6, 1),
            (5, -5, 2, 2, -6, 1),
            (-5, -5, -1, 2, 6, 0),
            (0, 13, 9, 3, 1, 1),
            (13, 0, -9, 3, -2, 7),
            (1, 1, 1, 256, 0, 2),
            (maxInt257, 1, 0, 256, 0, maxInt257),
            (minInt257, 1, 0, 256, -1, 0),
            (minInt257, -1, 0, 256, 1, 0),
            (maxInt257, -1, -1, 256, -1, 0),
            (maxInt257, maxInt257, maxInt257, 256, maxInt257, 0),
            (maxInt257, maxInt257, 0, 256, maxInt257 - 1, 1),
            (minInt257, minInt257, minInt257, 256, maxInt257, 0)
          ]
        for c in checks do
          let (x, y, w, shift, q, r) := c
          expectOkStack s!"/unit/direct/x={x}/y={y}/w={w}/shift={shift}"
            (runMuladdrshiftHashModDirect shift #[intV x, intV y, intV w])
            #[intV q, intV r] }
    ,
    { name := "/unit/pop-order/hash-immediate-preserves-lower-stack"
      run := do
        expectOkStack "/unit/pop-order/lower-null-preserved"
          (runMuladdrshiftHashModDirect 1 #[.null, intV 7, intV 3, intV 1])
          #[.null, intV 11, intV 0]
        expectOkStack "/unit/pop-order/lower-cell-preserved"
          (runMuladdrshiftHashModDirect 2 #[.cell Cell.empty, intV (-7), intV 3, intV 0])
          #[.cell Cell.empty, intV (-6), intV 3] }
    ,
    { name := "/unit/error/intov-underflow-type-and-pop-order"
      run := do
        expectErr "/unit/intov/overflow-max-max-plus-max-shift1"
          (runMuladdrshiftHashModDirect 1 #[intV maxInt257, intV maxInt257, intV maxInt257]) .intOv
        expectErr "/unit/intov/overflow-min-min-plus-min-shift1"
          (runMuladdrshiftHashModDirect 1 #[intV minInt257, intV minInt257, intV minInt257]) .intOv
        expectErr "/unit/intov/overflow-min-min-plus-zero-shift256"
          (runMuladdrshiftHashModDirect 256 #[intV minInt257, intV minInt257, intV 0]) .intOv
        expectErr "/unit/underflow/empty"
          (runMuladdrshiftHashModDirect 1 #[]) .stkUnd
        expectErr "/unit/underflow/one-int"
          (runMuladdrshiftHashModDirect 1 #[intV 7]) .stkUnd
        expectErr "/unit/underflow/two-int"
          (runMuladdrshiftHashModDirect 1 #[intV 7, intV 3]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-two-non-int"
          (runMuladdrshiftHashModDirect 1 #[.null, .cell Cell.empty]) .stkUnd
        expectErr "/unit/type/pop-w-first-null"
          (runMuladdrshiftHashModDirect 1 #[intV 7, intV 3, .null]) .typeChk
        expectErr "/unit/type/pop-w-first-cell"
          (runMuladdrshiftHashModDirect 1 #[intV 7, intV 3, .cell Cell.empty]) .typeChk
        expectErr "/unit/type/pop-y-second-null"
          (runMuladdrshiftHashModDirect 1 #[intV 7, .null, intV 1]) .typeChk
        expectErr "/unit/type/pop-x-third-null"
          (runMuladdrshiftHashModDirect 1 #[.null, intV 3, intV 1]) .typeChk
        expectErr "/unit/error-order/pop-w-before-y-when-both-non-int"
          (runMuladdrshiftHashModDirect 1 #[intV 7, .cell Cell.empty, .null]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-when-both-non-int"
          (runMuladdrshiftHashModDirect 1 #[.cell Cell.empty, .null, intV 1]) .typeChk }
    ,
    { name := "/unit/error/immediate-range-gate-precedence"
      run := do
        expectErr "/unit/error-order/underflow-before-range-invalid-immediate-empty"
          (runMuladdrshiftHashModDirect 257 #[]) .stkUnd
        expectErr "/unit/error-order/underflow-before-range-invalid-immediate-one-item"
          (runMuladdrshiftHashModDirect 257 #[intV 7]) .stkUnd
        expectErr "/unit/error-order/underflow-before-range-invalid-immediate-two-items"
          (runMuladdrshiftHashModDirect 257 #[intV 7, intV 3]) .stkUnd
        expectErr "/unit/range/immediate-overmax"
          (runMuladdrshiftHashModDirect 257 #[intV 7, intV 3, intV 1]) .rangeChk
        expectErr "/unit/error-order/range-before-w-type-invalid-immediate"
          (runMuladdrshiftHashModDirect 257 #[intV 7, intV 3, .null]) .rangeChk
        expectErr "/unit/error-order/range-before-y-type-invalid-immediate"
          (runMuladdrshiftHashModDirect 257 #[intV 7, .null, intV 1]) .rangeChk
        expectErr "/unit/error-order/range-before-x-type-invalid-immediate"
          (runMuladdrshiftHashModDirect 257 #[.null, intV 3, intV 1]) .rangeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkMuladdrshiftHashModInstr 1
        let instr256 := mkMuladdrshiftHashModInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/decode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/muladdrshift-hash-mod-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/muladdrshift-hash-mod-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/opcode/assemble-hash-immediate-range-checked"
      run := do
        expectAssembleErr "/unit/assemble/shift0-range"
          (mkMuladdrshiftHashModInstr 0) .rangeChk
        expectAssembleErr "/unit/assemble/shift257-range"
          (mkMuladdrshiftHashModInstr 257) .rangeChk }
    ,
    { name := "/unit/dispatch/non-muladdrshift-hash-mod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runMuladdrshiftHashModDispatchFallback #[]) #[intV 7461] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/floor/sign/pos-pos-shift1" 1 (.num 7) (.num 3) (.num 1),
    mkShiftInputCase "/ok/floor/sign/neg-pos-shift1" 1 (.num (-7)) (.num 3) (.num 1),
    mkShiftInputCase "/ok/floor/sign/pos-neg-shift1" 1 (.num 7) (.num (-3)) (.num 1),
    mkShiftInputCase "/ok/floor/sign/neg-neg-shift1" 1 (.num (-7)) (.num (-3)) (.num 1),
    mkShiftInputCase "/ok/floor/inexact/pos-pos-shift2" 2 (.num 5) (.num 5) (.num (-2)),
    mkShiftInputCase "/ok/floor/inexact/mixed-sign-shift2" 2 (.num 5) (.num (-5)) (.num 2),
    mkShiftInputCase "/ok/floor/exact/divisible-pos-shift3" 3 (.num 8) (.num 4) (.num 0),
    mkShiftInputCase "/ok/floor/exact/divisible-neg-shift3" 3 (.num (-8)) (.num 4) (.num 0),
    mkShiftInputCase "/ok/floor/zero-left-factor" 17 (.num 0) (.num 9) (.num 5),
    mkShiftInputCase "/ok/floor/zero-right-factor" 17 (.num 9) (.num 0) (.num (-5)),
    mkShiftInputCase "/ok/floor/zero-total-via-additive-cancel" 4 (.num 5) (.num 5) (.num (-25)),
    mkShiftInputCase "/ok/boundary/max-times-one-shift256" 256 (.num maxInt257) (.num 1) (.num 0),
    mkShiftInputCase "/ok/boundary/min-times-one-shift256" 256 (.num minInt257) (.num 1) (.num 0),
    mkShiftInputCase "/ok/boundary/min-times-negone-shift256" 256 (.num minInt257) (.num (-1)) (.num 0),
    mkShiftInputCase "/ok/boundary/max-times-negone-minusone-shift256"
      256 (.num maxInt257) (.num (-1)) (.num (-1)),
    mkShiftInputCase "/ok/boundary/max-times-max-plus-max-shift256"
      256 (.num maxInt257) (.num maxInt257) (.num maxInt257),
    mkShiftInputCase "/ok/boundary/max-times-max-plus-zero-shift256"
      256 (.num maxInt257) (.num maxInt257) (.num 0),
    mkShiftInputCase "/ok/boundary/min-times-min-plus-min-shift256"
      256 (.num minInt257) (.num minInt257) (.num minInt257),
    mkShiftStackCase "/ok/pop-order/lower-null-preserved" 1 #[.null, intV 7, intV 3, intV 1],
    mkShiftStackCase "/ok/pop-order/lower-cell-preserved" 2 #[.cell Cell.empty, intV (-7), intV 3, intV 0],
    mkShiftInputCase "/intov/overflow-max-max-plus-max-shift1"
      1 (.num maxInt257) (.num maxInt257) (.num maxInt257),
    mkShiftInputCase "/intov/overflow-min-min-plus-min-shift1"
      1 (.num minInt257) (.num minInt257) (.num minInt257),
    mkShiftInputCase "/intov/overflow-min-min-plus-zero-shift256"
      256 (.num minInt257) (.num minInt257) (.num 0),
    mkShiftStackCase "/underflow/empty-stack" 1 #[],
    mkShiftStackCase "/underflow/one-int" 1 #[intV 7],
    mkShiftStackCase "/underflow/two-ints" 1 #[intV 7, intV 3],
    mkShiftStackCase "/error-order/underflow-before-type-two-non-int" 1 #[.null, .cell Cell.empty],
    mkShiftStackCase "/type/pop-w-first-null" 1 #[intV 7, intV 3, .null],
    mkShiftStackCase "/type/pop-w-first-cell" 1 #[intV 7, intV 3, .cell Cell.empty],
    mkShiftStackCase "/type/pop-y-second-null" 1 #[intV 7, .null, intV 1],
    mkShiftStackCase "/type/pop-x-third-null" 1 #[.null, intV 3, intV 1],
    mkShiftStackCase "/error-order/pop-w-before-y-when-both-non-int"
      1 #[intV 7, .cell Cell.empty, .null],
    mkShiftStackCase "/error-order/pop-y-before-x-when-both-non-int"
      1 #[.cell Cell.empty, .null, intV 1],
    mkShiftInputCase "/intov/nan-x-via-program" 1 .nan (.num 3) (.num 1),
    mkShiftInputCase "/intov/nan-y-via-program" 1 (.num 7) .nan (.num 1),
    mkShiftInputCase "/intov/nan-w-via-program" 1 (.num 7) (.num 3) .nan,
    mkShiftInputCase "/intov/nan-all-via-program" 1 .nan .nan .nan,
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op"
      1 (.num (maxInt257 + 1)) (.num 3) (.num 1),
    mkShiftInputCase "/error-order/pushint-overflow-y-before-op"
      1 (.num 7) (.num (minInt257 - 1)) (.num 1),
    mkShiftInputCase "/error-order/pushint-overflow-w-before-op"
      1 (.num 7) (.num 3) (.num (maxInt257 + 1)),
    mkShiftInputCase "/error-order/pushint-overflow-all-before-op"
      1 (.num (pow2 257)) (.num (-(pow2 257))) (.num (pow2 257)),
    mkCase "/error-order/pushint-overflow-before-op-type-check" #[.null]
      #[.pushInt (.num (pow2 257)), mkMuladdrshiftHashModInstr 1],
    mkCase "/error-order/pushint-overflow-before-op-underflow" #[]
      #[.pushInt (.num (-(pow2 257))), mkMuladdrshiftHashModInstr 1],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num muladdrshiftHashModSetGasExact), .tonEnvOp .setGasLimit, muladdrshiftHashModGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 1]
      #[.pushInt (.num muladdrshiftHashModSetGasExactMinusOne), .tonEnvOp .setGasLimit, muladdrshiftHashModGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020895
      count := 700
      gen := genMuladdrshiftHashModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULADDRSHIFT_HASH_MOD
