import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULRSHIFTC_HASH_MOD

/-
MULRSHIFTC#MOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod true false 3 1 false (some z)` specialization)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type/overflow ordering)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, `modPow2Round`, ceil quotient/remainder invariants)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` + `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (current Lean codec gap for `0xa9b*` non-add MUL hash forms)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod` mode=2 hash-immediate path, `dump_mulshrmod`, `register_div_ops`)

Branch/terminal counts used for this suite
(`mul=true`, `add=false`, `d=3`, `roundMode=1`, `quiet=false`, `zOpt=some z`):
- Lean specialization: ~8 branch sites / ~11 terminal outcomes
  (dispatch/fallback; underflow precheck; immediate range guard; `y`/`x` pop type split;
   finite-vs-NaN split; round guard; `d=3` dual-result non-quiet overflow funnels).
- C++ specialization (`exec_mulshrmod`, mode=2): ~8 branch sites / ~11 aligned outcomes
  (hash-arg decode; add-remap/op validity; underflow gate; `z=0` round normalization;
   global-version invalid-input funnel; `d` switch; non-quiet push overflow funnel).

Key risk areas covered:
- ceil quotient/remainder semantics for mixed signs and near-half residues;
- boundary shifts (`1`, `255`, `256`) and signed-257 multiplication cliffs;
- strict pop/error order (`y` then `x`; underflow before type; range before pops);
- NaN/out-of-range injection only via program prelude helpers in oracle/fuzz paths;
- exact gas boundary for executable surrogate
  `PUSHINT n ; SETGASLIMIT ; PUSHINT z ; MULRSHIFTCMOD`.

Executable-note:
- Lean currently does not assemble/decode the direct hash opcode form for this mnemonic.
  Unit tests execute direct hash semantics (`zOpt=some z`) via handler calls.
  Oracle/fuzz cases use the executable semantic surrogate `PUSHINT z ; MULRSHIFTCMOD`.
-/

private def mulrshiftcHashModId : InstrId := { name := "MULRSHIFTC#MOD" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkMulrshiftcHashModInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod true false 3 1 false (some shift))

private def mulrshiftcmodRuntimeInstr : Instr :=
  .arithExt (.shrMod true false 3 1 false none)

private def mkOracleProgram (shift : Nat) : Array Instr :=
  #[.pushInt (.num (Int.ofNat shift)), mulrshiftcmodRuntimeInstr]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := mkOracleProgram 1)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := mulrshiftcHashModId
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
  mkCase name stack (mkOracleProgram shift) gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (programPrefix ++ mkOracleProgram shift) gasLimits fuel

private def runMulrshiftcHashModDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkMulrshiftcHashModInstr shift) stack

private def runMulrshiftcmodRuntimeDirect
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt mulrshiftcmodRuntimeInstr stack

private def runMulrshiftcHashModDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9463)) stack

private def expectSameResult
    (label : String)
    (lhs rhs : Except Excno (Array Value)) : IO Unit := do
  match lhs, rhs with
  | .ok a, .ok b =>
      if a == b then
        pure ()
      else
        throw (IO.userError s!"{label}: result mismatch; lhs={reprStr a}, rhs={reprStr b}")
  | .error e1, .error e2 =>
      if e1 == e2 then
        pure ()
      else
        throw (IO.userError s!"{label}: error mismatch; lhs={e1}, rhs={e2}")
  | .ok a, .error e =>
      throw (IO.userError s!"{label}: lhs succeeded with {reprStr a}, rhs errored with {e}")
  | .error e, .ok b =>
      throw (IO.userError s!"{label}: lhs errored with {e}, rhs succeeded with {reprStr b}")

private def expectAssembleErr (label : String) (program : List Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 program with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error err =>
      if err = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {err}")

private def gasForInstrOrFallback (instr : Instr) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok budget => budget
  | .error _ => instrGas instr 16

private def setGasNeedForOracleShift (shift : Nat) (n : Int) : Int :=
  gasForInstrOrFallback (.pushInt (.num n))
    + gasForInstrOrFallback (.tonEnvOp .setGasLimit)
    + gasForInstrOrFallback (.pushInt (.num (Int.ofNat shift)))
    + gasForInstrOrFallback mulrshiftcmodRuntimeInstr
    + implicitRetGasPrice

private def exactGasBudgetFixedPointForOracleShift (shift : Nat) (n : Int) : Nat → Int
  | 0 => n
  | k + 1 =>
      let n' := setGasNeedForOracleShift shift n
      if n' = n then n else exactGasBudgetFixedPointForOracleShift shift n' k

private def exactGasBudgetForOracleShift (shift : Nat) : Int :=
  exactGasBudgetFixedPointForOracleShift shift 64 16

private def exactGasBudgetMinusOneForOracleShift (shift : Nat) : Int :=
  let budget := exactGasBudgetForOracleShift shift
  if budget > 0 then budget - 1 else 0

private def mulrshiftcHashModSetGasExactShift1 : Int :=
  exactGasBudgetForOracleShift 1

private def mulrshiftcHashModSetGasExactMinusOneShift1 : Int :=
  exactGasBudgetMinusOneForOracleShift 1

private def mulrshiftcHashModSetGasExactShift256 : Int :=
  exactGasBudgetForOracleShift 256

private def mulrshiftcHashModSetGasExactMinusOneShift256 : Int :=
  exactGasBudgetMinusOneForOracleShift 256

private def mkGasProgram (budget : Int) (shift : Nat) : Array Instr :=
  #[.pushInt (.num budget), .tonEnvOp .setGasLimit] ++ mkOracleProgram shift

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tinyShiftPool : Array Nat :=
  #[1, 2, 3, 4, 5, 6, 7, 8]

private def smallSignedPool : Array Int :=
  #[-33, -17, -13, -9, -7, -5, -3, -2, -1, 0, 1, 2, 3, 5, 7, 9, 13, 17, 33]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickFromNatPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromNatPool shiftBoundaryPool rng

private def pickShiftInRange (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 1 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  (if pickCell then .cell Cell.empty else .null, rng')

private def classifyMulrshiftcHashMod (x y : Int) (shift : Nat) : String :=
  let tmp : Int := x * y
  let q := rshiftPow2Round tmp shift 1
  let r := modPow2Round tmp shift 1
  if !intFitsSigned257 q || !intFitsSigned257 r then
    "overflow"
  else if tmp = 0 then
    "zero"
  else if r = 0 then
    "exact"
  else if tmp < 0 then
    "inexact-neg"
  else
    "inexact-pos"

private def mkFiniteFuzzCase (shape : Nat) (x y : Int) (shift : Nat) : OracleCase :=
  let kind := classifyMulrshiftcHashMod x y shift
  mkShiftCase s!"/fuzz/shape-{shape}/{kind}" shift #[intV x, intV y]

private def genMulrshiftcHashModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 23
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 4 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkFiniteFuzzCase shape 0 y shift, r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkFiniteFuzzCase shape x 0 shift, r3)
    else if shape = 6 then
      let (useMax, r2) := randBool rng1
      let (useNegY, r3) := randBool r2
      let x := if useMax then maxInt257 else minInt257
      let y := if useNegY then (-1) else 1
      (mkFiniteFuzzCase shape x y 256, r3)
    else if shape = 7 then
      (mkShiftCase s!"/fuzz/shape-{shape}/overflow/max-max-shift1"
        1 #[intV maxInt257, intV maxInt257], rng1)
    else if shape = 8 then
      (mkShiftCase s!"/fuzz/shape-{shape}/overflow/min-min-shift1"
        1 #[intV minInt257, intV minInt257], rng1)
    else if shape = 9 then
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty-stack" 1 #[], rng1)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/one-item" 1 #[intV x], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/y-pop-first" shift #[intV x, yLike], r4)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      let (xLike, r3) := pickNonInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/x-pop-second" shift #[xLike, intV y], r4)
    else if shape = 13 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/y-before-x-when-both-non-int"
        shift #[.null, .cell Cell.empty], r2)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      let (below, r5) := pickNonInt r4
      (mkShiftCase s!"/fuzz/shape-{shape}/pop-order/below-preserved"
        shift #[below, intV x, intV y], r5)
    else if shape = 15 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program"
        shift #[.nan, .num y], r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-y-via-program"
        shift #[.num x, .nan], r3)
    else if shape = 17 then
      let (oor, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/range/x-via-program"
        shift #[.num oor, .num y], r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (oor, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/range/y-via-program"
        shift #[.num x, .num oor], r4)
    else if shape = 19 then
      let (oor, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-type-check"
        shift #[.num oor, .num 3] #[.null], r3)
    else if shape = 20 then
      let (oor, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-underflow"
        shift #[.num oor], r3)
    else if shape = 21 then
      let (qSeed, r2) := pickFromIntPool smallSignedPool rng1
      let (shift, r3) := pickFromNatPool tinyShiftPool r2
      let x := qSeed * pow2 shift
      (mkFiniteFuzzCase shape x 1 shift, r3)
    else if shape = 22 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkFiniteFuzzCase shape x y 256, r3)
    else if shape = 23 then
      let (xRaw, r2) := pickSigned257ish rng1
      let x := if xRaw = 0 then 1 else xRaw
      let (shift, r3) := pickShiftInRange r2
      (mkFiniteFuzzCase shape x (-1) shift, r3)
    else
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/fallback" 1 #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulrshiftcHashModId
  unit := #[
    { name := "/unit/direct/ceil-rounding-sign-and-boundary-invariants"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (7, 3, 1, 11, -1),
            (-7, 3, 1, -10, -1),
            (7, -3, 1, -10, -1),
            (-7, -3, 1, 11, -1),
            (5, 5, 2, 7, -3),
            (-5, 5, 2, -6, -1),
            (5, -5, 2, -6, -1),
            (-5, -5, 2, 7, -3),
            (0, 9, 5, 0, 0),
            (9, 0, 5, 0, 0),
            (maxInt257, 1, 256, 1, -1),
            (minInt257, 1, 256, -1, 0),
            (minInt257 + 1, 1, 256, 0, minInt257 + 1),
            (minInt257, -1, 1, pow2 255, 0),
            (maxInt257, -1, 1, 1 - (pow2 255), -1)
          ]
        for c in checks do
          match c with
          | (x, y, shift, q, r) =>
              expectOkStack s!"/unit/direct/x={x}/y={y}/z={shift}"
                (runMulrshiftcHashModDirect shift #[intV x, intV y])
                #[intV q, intV r] }
    ,
    { name := "/unit/pop-order/hash-immediate-does-not-pop-below-item"
      run := do
        expectOkStack "/unit/pop-order/lower-null-preserved"
          (runMulrshiftcHashModDirect 1 #[.null, intV 7, intV 3]) #[.null, intV 11, intV (-1)]
        expectOkStack "/unit/pop-order/lower-cell-preserved"
          (runMulrshiftcHashModDirect 1 #[.cell Cell.empty, intV (-7), intV 3])
          #[.cell Cell.empty, intV (-10), intV (-1)]
        expectOkStack "/unit/pop-order/lower-int-preserved"
          (runMulrshiftcHashModDirect 2 #[intV 42, intV 5, intV 5])
          #[intV 42, intV 7, intV (-3)] }
    ,
    { name := "/unit/error/intov-underflow-type-range-and-order"
      run := do
        expectErr "/unit/error/intov/max-times-max-shift1"
          (runMulrshiftcHashModDirect 1 #[intV maxInt257, intV maxInt257]) .intOv
        expectErr "/unit/error/intov/min-times-min-shift1"
          (runMulrshiftcHashModDirect 1 #[intV minInt257, intV minInt257]) .intOv
        expectErr "/unit/error/underflow/empty"
          (runMulrshiftcHashModDirect 1 #[]) .stkUnd
        expectErr "/unit/error/underflow/one-item"
          (runMulrshiftcHashModDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-single-non-int"
          (runMulrshiftcHashModDirect 1 #[.null]) .stkUnd
        expectErr "/unit/error/type/y-pop-first-null"
          (runMulrshiftcHashModDirect 1 #[intV 5, .null]) .typeChk
        expectErr "/unit/error/type/y-pop-first-cell"
          (runMulrshiftcHashModDirect 1 #[intV 5, .cell Cell.empty]) .typeChk
        expectErr "/unit/error/type/x-pop-second-null"
          (runMulrshiftcHashModDirect 1 #[.null, intV 5]) .typeChk
        expectErr "/unit/error-order/y-before-x-when-both-non-int"
          (runMulrshiftcHashModDirect 1 #[.null, .cell Cell.empty]) .typeChk
        expectErr "/unit/error-order/underflow-before-range-invalid-immediate"
          (runMulrshiftcHashModDirect 257 #[]) .stkUnd
        expectErr "/unit/error-order/range-before-y-type-invalid-immediate"
          (runMulrshiftcHashModDirect 257 #[intV 5, .null]) .rangeChk
        expectErr "/unit/error-order/range-before-x-type-invalid-immediate"
          (runMulrshiftcHashModDirect 257 #[.null, intV 5]) .rangeChk }
    ,
    { name := "/unit/surrogate/runtime-prelude-matches-hash-semantics"
      run := do
        let checks : Array (Array Value × Nat) :=
          #[
            (#[intV 7, intV 3], 1),
            (#[intV (-7), intV 3], 1),
            (#[intV 5, intV (-5)], 2),
            (#[intV minInt257, intV (-1)], 1),
            (#[.null, intV 7, intV 3], 1),
            (#[.cell Cell.empty, intV (-7), intV 3], 1),
            (#[], 1),
            (#[intV 1], 1),
            (#[intV 5, .null], 1),
            (#[.null, intV 5], 1)
          ]
        for c in checks do
          match c with
          | (stack, shift) =>
              let direct := runMulrshiftcHashModDirect shift stack
              let runtimeStack := stack.push (intV (Int.ofNat shift))
              let surrogate := runMulrshiftcmodRuntimeDirect runtimeStack
              expectSameResult s!"/unit/surrogate/shift={shift}/stack={reprStr stack}" direct surrogate }
    ,
    { name := "/unit/opcode/hash-form-encoding-range-gates"
      run := do
        match assembleCp0 [mkMulrshiftcHashModInstr 1] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"/unit/opcode/encode/hash-form-z1: expected success, got {e}")
        match assembleCp0 [mkMulrshiftcHashModInstr 256] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"/unit/opcode/encode/hash-form-z256: expected success, got {e}") }
    ,
    { name := "/unit/dispatch/non-mulrshiftc-hash-mod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runMulrshiftcHashModDispatchFallback #[]) #[intV 9463] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/ceil/sign/pos-pos-shift1" 1 #[.num 7, .num 3],
    mkShiftInputCase "/ok/ceil/sign/neg-pos-shift1" 1 #[.num (-7), .num 3],
    mkShiftInputCase "/ok/ceil/sign/pos-neg-shift1" 1 #[.num 7, .num (-3)],
    mkShiftInputCase "/ok/ceil/sign/neg-neg-shift1" 1 #[.num (-7), .num (-3)],
    mkShiftInputCase "/ok/ceil/sign/pos-pos-shift2" 2 #[.num 5, .num 5],
    mkShiftInputCase "/ok/ceil/sign/neg-pos-shift2" 2 #[.num (-5), .num 5],
    mkShiftInputCase "/ok/ceil/sign/pos-neg-shift2" 2 #[.num 5, .num (-5)],
    mkShiftInputCase "/ok/ceil/sign/neg-neg-shift2" 2 #[.num (-5), .num (-5)],
    mkShiftInputCase "/ok/exact/zero-left-factor" 5 #[.num 0, .num 9],
    mkShiftInputCase "/ok/exact/zero-right-factor" 5 #[.num 9, .num 0],
    mkShiftInputCase "/ok/boundary/max-times-one-shift256" 256 #[.num maxInt257, .num 1],
    mkShiftInputCase "/ok/boundary/min-times-one-shift256" 256 #[.num minInt257, .num 1],
    mkShiftInputCase "/ok/boundary/min-plus-one-times-one-shift256" 256 #[.num (minInt257 + 1), .num 1],
    mkShiftInputCase "/ok/boundary/min-times-neg-one-shift1" 1 #[.num minInt257, .num (-1)],
    mkShiftInputCase "/ok/boundary/max-times-neg-one-shift1" 1 #[.num maxInt257, .num (-1)],
    mkShiftCase "/ok/pop-order/lower-null-preserved" 1 #[.null, intV 7, intV 3],
    mkShiftCase "/ok/pop-order/lower-cell-preserved" 1 #[.cell Cell.empty, intV (-7), intV 3],
    mkShiftCase "/ok/pop-order/lower-int-preserved" 2 #[intV 42, intV 5, intV 5],
    mkShiftInputCase "/overflow/max-times-max-shift1" 1 #[.num maxInt257, .num maxInt257],
    mkShiftInputCase "/overflow/min-times-min-shift1" 1 #[.num minInt257, .num minInt257],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/underflow/one-item" 1 #[intV 1],
    mkShiftCase "/error-order/underflow-before-type-single-non-int" 1 #[.null],
    mkShiftCase "/type/y-pop-first-null" 1 #[intV 5, .null],
    mkShiftCase "/type/y-pop-first-cell" 1 #[intV 5, .cell Cell.empty],
    mkShiftCase "/type/x-pop-second-null" 1 #[.null, intV 5],
    mkShiftCase "/type/x-pop-second-cell" 1 #[.cell Cell.empty, intV 5],
    mkShiftCase "/error-order/y-before-x-when-both-non-int" 1 #[.null, .cell Cell.empty],
    mkShiftInputCase "/intov/nan-x-via-program" 1 #[.nan, .num 3],
    mkShiftInputCase "/intov/nan-y-via-program" 1 #[.num 5, .nan],
    mkShiftInputCase "/range/x-high-via-program" 1 #[.num (maxInt257 + 1), .num 3],
    mkShiftInputCase "/range/x-low-via-program" 1 #[.num (minInt257 - 1), .num 3],
    mkShiftInputCase "/range/y-high-via-program" 1 #[.num 5, .num (maxInt257 + 1)],
    mkShiftInputCase "/range/y-low-via-program" 1 #[.num 5, .num (minInt257 - 1)],
    mkShiftInputCase "/error-order/pushint-overflow-before-op-type-check"
      1 #[.num (pow2 257), .num 3] #[.null],
    mkShiftInputCase "/error-order/pushint-overflow-before-op-underflow"
      1 #[.num (-(pow2 257))],
    mkCase "/gas/exact-cost-succeeds/shift1" #[intV 7, intV 5]
      (mkGasProgram mulrshiftcHashModSetGasExactShift1 1),
    mkCase "/gas/exact-minus-one-out-of-gas/shift1" #[intV 7, intV 5]
      (mkGasProgram mulrshiftcHashModSetGasExactMinusOneShift1 1),
    mkCase "/gas/exact-cost-succeeds/shift256" #[intV 7, intV 5]
      (mkGasProgram mulrshiftcHashModSetGasExactShift256 256),
    mkCase "/gas/exact-minus-one-out-of-gas/shift256" #[intV 7, intV 5]
      (mkGasProgram mulrshiftcHashModSetGasExactMinusOneShift256 256)
  ]
  fuzz := #[
    { seed := 2026020903
      count := 768
      gen := genMulrshiftcHashModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFTC_HASH_MOD
