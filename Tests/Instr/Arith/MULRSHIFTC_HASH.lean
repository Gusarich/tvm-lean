import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULRSHIFTC_HASH

/-
MULRSHIFTC# branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod true false 1 1 false (some z))` path)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`, underflow/type/overflow behavior)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate MULRSHIFT* `mul=true/add=false` currently rejected as `.invOpcode`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (24-bit hash-immediate decode currently covers `0xa930..0xa93e`, `0xa9b0..0xa9b2`, `0xa9d0..0xa9de`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite:
- Lean direct semantic path (`mul=true`, `add=false`, `d=1`, `round=ceil`, `zOpt=some`):
  9 branch sites / 14 terminal outcomes
  (dispatch/fallback; underflow gate; runtime-shift range gate; `y` pop type path;
   `x` pop type path; numeric-vs-NaN funnel; round-mode validity; `d` switch;
   non-quiet push fit-vs-`intOv`).
- Lean cp0-executable lowering used for oracle/fuzz (`PUSHINT z; MULRSHIFTC`):
  8 branch sites / 13 terminal outcomes
  (runtime-shift pop/type/range ordering, then same numeric/overflow funnel).
- C++ `exec_mulshrmod` aligned path:
  8 branch sites / 13 aligned terminal outcomes
  (depth/range/type gates, arithmetic branch, non-quiet push funnel).

Key risk areas covered:
- ceil rounding on odd products across sign combinations and boundary shifts (`1`, `255`, `256`);
- hash-immediate pop discipline (`x,y` only) with below-stack preservation;
- strict error ordering (`stkUnd` before type on short stacks, `y` pop before `x`);
- range-before-type ordering when lowered runtime shift is out of range;
- NaN/out-of-range operand injection only via `PUSHINT` prelude helpers;
- current cp0 encode gap for MULRSHIFTC# is unit-tested explicitly;
- gas cliff oracle probes use shared exact-budget helpers.
-/

private def mulrshiftcHashId : InstrId := { name := "MULRSHIFTC#" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkMulrshiftcHashInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod true false 1 1 false (some shift))

private def mulrshiftcRuntimeInstr : Instr :=
  .arithExt (.shrMod true false 1 1 false none)

private def loweredProgram (shift : Nat) (programPrefix : Array Instr := #[]) : Array Instr :=
  programPrefix ++ #[.pushInt (.num (Int.ofNat shift)), mulrshiftcRuntimeInstr]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := loweredProgram 1)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := mulrshiftcHashId
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
  mkCase name stack (loweredProgram shift) gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (x y : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram #[x, y]
  mkCase name (below ++ stack) (loweredProgram shift programPrefix) gasLimits fuel

private def mkRuntimeShiftCase
    (name : String)
    (shiftRaw : Int)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[.pushInt (.num shiftRaw), mulrshiftcRuntimeInstr] gasLimits fuel

private def runMulrshiftcHashDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkMulrshiftcHashInstr shift) stack

private def runMulrshiftcHashLoweredDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt mulrshiftcRuntimeInstr (stack.push (intV (Int.ofNat shift)))

private def runMulrshiftcHashDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9476)) stack

private def expectSameResult
    (label : String)
    (lhs rhs : Except Excno (Array Value)) : IO Unit := do
  match lhs, rhs with
  | .ok a, .ok b =>
      if a == b then
        pure ()
      else
        throw (IO.userError s!"{label}: mismatch lhs={reprStr a} rhs={reprStr b}")
  | .error e1, .error e2 =>
      if e1 == e2 then
        pure ()
      else
        throw (IO.userError s!"{label}: mismatch lhsErr={e1} rhsErr={e2}")
  | _, _ =>
      throw (IO.userError s!"{label}: mismatch lhs={reprStr lhs} rhs={reprStr rhs}")

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

private def mulrshiftcHashGasProbeInstr : Instr :=
  mulrshiftcRuntimeInstr

private def mulrshiftcHashSetGasExact : Int :=
  computeExactGasBudget mulrshiftcHashGasProbeInstr

private def mulrshiftcHashSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulrshiftcHashGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tinyShiftPool : Array Nat :=
  #[1, 2, 3, 4, 5, 6, 7, 8]

private def shiftOutOfRangePool : Array Int :=
  #[-7, -3, -1, 257, 258, 300, 511]

private def smallSignedPool : Array Int :=
  #[-33, -17, -13, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 13, 17, 33]

private def pickFromNatPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromNatPool shiftBoundaryPool rng

private def pickTinyShift (rng : StdGen) : Nat × StdGen :=
  pickFromNatPool tinyShiftPool rng

private def pickShiftInRange (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 1 256

private def pickShiftOutOfRange (rng : StdGen) : Int × StdGen :=
  pickFromIntPool shiftOutOfRangePool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  (if pickCell then .cell Cell.empty else .null, rng')

private def classifyMulrshiftcHash (x y : Int) (shift : Nat) : String :=
  let prod := x * y
  let q := rshiftPow2Round prod shift 1
  if !intFitsSigned257 q then
    "intov-overflow"
  else if q * intPow2 shift = prod then
    "ok-exact"
  else
    "ok-inexact"

private def mkFiniteFuzzCase (shape : Nat) (x y : Int) (shift : Nat) : OracleCase :=
  let kind := classifyMulrshiftcHash x y shift
  mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}" shift #[intV x, intV y]

private def genMulrshiftcHashFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftInRange r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 4 then
      let (x, r2) := pickFromIntPool smallSignedPool rng1
      let (y, r3) := pickFromIntPool smallSignedPool r2
      let (shift, r4) := pickTinyShift r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 5 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkFiniteFuzzCase shape 0 y shift, r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkFiniteFuzzCase shape x 0 shift, r3)
    else if shape = 7 then
      let (pickMin, r2) := randBool rng1
      let x := if pickMin then minInt257 else maxInt257
      let (y, r3) := pickFromIntPool smallSignedPool r2
      (mkFiniteFuzzCase shape x y 1, r3)
    else if shape = 8 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      (mkFiniteFuzzCase shape x y 256, r3)
    else if shape = 9 then
      (mkShiftStackCase s!"/fuzz/shape-{shape}/intov-overflow/max-max-shift255"
        255 #[intV maxInt257, intV maxInt257], rng1)
    else if shape = 10 then
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/empty-stack" 1 #[], rng1)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/one-arg" 1 #[intV x], r2)
    else if shape = 12 then
      let (xLike, r2) := pickNonInt rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/one-non-int-before-type"
        1 #[xLike], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/pop-y-first"
        shift #[intV x, yLike], r4)
    else if shape = 14 then
      let (xLike, r2) := pickNonInt rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/pop-x-second"
        shift #[xLike, intV y], r4)
    else if shape = 15 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-both-non-int"
        shift #[.null, .cell Cell.empty], r2)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let (below, r5) := pickNonInt r4
      (mkShiftStackCase s!"/fuzz/shape-{shape}/pop-order/hash-immediate-does-not-pop-below"
        shift #[below, intV x, intV y], r5)
    else if shape = 17 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/x-via-program"
        shift .nan (.num y), r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/y-via-program"
        shift (.num x) .nan, r3)
    else if shape = 19 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/range/x-out-of-range-via-program"
        shift (.num xOut) (.num y), r4)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/range/y-out-of-range-via-program"
        shift (.num x) (.num yOut), r4)
    else if shape = 21 then
      let (shiftRaw, r2) := pickShiftOutOfRange rng1
      let (x, r3) := pickSigned257ish r2
      let (yLike, r4) := pickNonInt r3
      (mkRuntimeShiftCase s!"/fuzz/shape-{shape}/error-order/range-before-y-type-in-lowered-path"
        shiftRaw #[intV x, yLike], r4)
    else
      let (shiftRaw, r2) := pickShiftOutOfRange rng1
      let (v, r3) := pickNonInt r2
      (mkRuntimeShiftCase s!"/fuzz/shape-{shape}/error-order/underflow-before-range-on-short-stack"
        shiftRaw #[v], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulrshiftcHashId
  unit := #[
    { name := "/unit/direct/ceil-rounding-sign-cases"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (7, 5, 1, 18),
            (-7, 5, 1, -17),
            (7, -5, 1, -17),
            (-7, -5, 1, 18),
            (7, 5, 2, 9),
            (-7, 5, 2, -8),
            (7, -5, 2, -8),
            (-7, -5, 2, 9),
            (5, 5, 2, 7),
            (-5, 5, 2, -6),
            (1, 1, 1, 1),
            (-1, 1, 1, 0),
            (1, -1, 1, 0),
            (-1, -1, 1, 1)
          ]
        for c in checks do
          match c with
          | (x, y, shift, expected) =>
              expectOkStack s!"/unit/direct/x={x}/y={y}/z={shift}"
                (runMulrshiftcHashDirect shift #[intV x, intV y])
                #[intV expected] }
    ,
    { name := "/unit/direct/boundary-and-pop-order"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (maxInt257, 1, 1, pow2 255),
            (minInt257, 1, 1, -(pow2 255)),
            (maxInt257, 1, 256, 1),
            (minInt257, 1, 256, -1),
            (maxInt257, -1, 256, 0),
            (maxInt257, maxInt257, 256, maxInt257),
            (minInt257, maxInt257, 256, minInt257 + 1),
            (0, maxInt257, 13, 0)
          ]
        for c in checks do
          match c with
          | (x, y, shift, expected) =>
              expectOkStack s!"/unit/boundary/x={x}/y={y}/z={shift}"
                (runMulrshiftcHashDirect shift #[intV x, intV y])
                #[intV expected]
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runMulrshiftcHashDirect 1 #[.null, intV 7, intV 5])
          #[.null, intV 18]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runMulrshiftcHashDirect 256 #[.cell Cell.empty, intV (-1), intV 1])
          #[.cell Cell.empty, intV 0] }
    ,
    { name := "/unit/error/underflow-type-intov-and-ordering"
      run := do
        expectErr "/unit/error/intov/max-max-shift255"
          (runMulrshiftcHashDirect 255 #[intV maxInt257, intV maxInt257]) .intOv
        expectErr "/unit/error/intov/min-min-shift255"
          (runMulrshiftcHashDirect 255 #[intV minInt257, intV minInt257]) .intOv
        expectErr "/unit/error/underflow/empty-stack"
          (runMulrshiftcHashDirect 1 #[]) .stkUnd
        expectErr "/unit/error/underflow/one-arg"
          (runMulrshiftcHashDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/error/order/underflow-before-type-one-non-int"
          (runMulrshiftcHashDirect 1 #[.null]) .stkUnd
        expectErr "/unit/error/type/pop-y-first"
          (runMulrshiftcHashDirect 1 #[intV 1, .null]) .typeChk
        expectErr "/unit/error/type/pop-x-second"
          (runMulrshiftcHashDirect 1 #[.null, intV 1]) .typeChk
        expectErr "/unit/error/order/pop-y-before-x-both-non-int"
          (runMulrshiftcHashDirect 1 #[.null, .cell Cell.empty]) .typeChk
        expectErr "/unit/error/order/range257-before-pop-type"
          (runMulrshiftcHashDirect 257 #[intV 1, .null]) .rangeChk
        expectErr "/unit/error/order/underflow-before-range257"
          (runMulrshiftcHashDirect 257 #[.null]) .stkUnd }
    ,
    { name := "/unit/lowering/direct-hash-matches-cp0-executable-lowering"
      run := do
        let checks : Array (Nat × Array Value) :=
          #[
            (1, #[intV 7, intV 5]),
            (256, #[intV maxInt257, intV 1]),
            (1, #[.null, intV 7, intV 5]),
            (1, #[intV 1, .null]),
            (1, #[.null, intV 1]),
            (1, #[]),
            (255, #[intV maxInt257, intV maxInt257]),
            (257, #[intV 1, .null])
          ]
        for c in checks do
          match c with
          | (shift, stack) =>
              expectSameResult s!"/unit/lowering/z={shift}/stack={reprStr stack}"
                (runMulrshiftcHashDirect shift stack)
                (runMulrshiftcHashLoweredDirect shift stack) }
    ,
    { name := "/unit/opcode/encode-gap-and-range-gates"
      run := do
        match assembleCp0 [mkMulrshiftcHashInstr 1] with
        | .ok _ => pure ()
        | .error e =>
            throw (IO.userError s!"/unit/opcode/encode/mulrshiftc-hash-z1-current-gap: expected success, got {e}")
        expectAssembleErr "/unit/opcode/encode/mulrshiftc-hash-z0-range"
          [mkMulrshiftcHashInstr 0] .rangeChk
        expectAssembleErr "/unit/opcode/encode/mulrshiftc-hash-z257-range"
          [mkMulrshiftcHashInstr 257] .rangeChk }
    ,
    { name := "/unit/dispatch/non-shrmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runMulrshiftcHashDispatchFallback #[]) #[intV 9476] }
  ]
  oracle := #[
    mkShiftStackCase "/ok/ceil/sign/pos-pos-shift1" 1 #[intV 7, intV 5],
    mkShiftStackCase "/ok/ceil/sign/neg-pos-shift1" 1 #[intV (-7), intV 5],
    mkShiftStackCase "/ok/ceil/sign/pos-neg-shift1" 1 #[intV 7, intV (-5)],
    mkShiftStackCase "/ok/ceil/sign/neg-neg-shift1" 1 #[intV (-7), intV (-5)],
    mkShiftStackCase "/ok/ceil/sign/pos-pos-shift2" 2 #[intV 7, intV 5],
    mkShiftStackCase "/ok/ceil/sign/neg-pos-shift2" 2 #[intV (-7), intV 5],
    mkShiftStackCase "/ok/ceil/sign/pos-neg-shift2" 2 #[intV 7, intV (-5)],
    mkShiftStackCase "/ok/ceil/sign/neg-neg-shift2" 2 #[intV (-7), intV (-5)],
    mkShiftStackCase "/ok/ceil/tie/neg-half-to-zero" 1 #[intV (-1), intV 1],
    mkShiftStackCase "/ok/ceil/tie/pos-half-to-one" 1 #[intV 1, intV 1],
    mkShiftStackCase "/ok/exact/zero-left-factor" 17 #[intV 0, intV 123],
    mkShiftStackCase "/ok/exact/zero-right-factor" 17 #[intV 123, intV 0],
    mkShiftStackCase "/ok/boundary/max-times-one-shift1" 1 #[intV maxInt257, intV 1],
    mkShiftStackCase "/ok/boundary/min-times-one-shift1" 1 #[intV minInt257, intV 1],
    mkShiftStackCase "/ok/boundary/max-times-one-shift256" 256 #[intV maxInt257, intV 1],
    mkShiftStackCase "/ok/boundary/min-times-one-shift256" 256 #[intV minInt257, intV 1],
    mkShiftStackCase "/ok/boundary/max-times-neg-one-shift256" 256 #[intV maxInt257, intV (-1)],
    mkShiftStackCase "/ok/boundary/max-times-max-shift256" 256 #[intV maxInt257, intV maxInt257],
    mkShiftStackCase "/ok/boundary/min-times-max-shift256" 256 #[intV minInt257, intV maxInt257],
    mkShiftStackCase "/ok/pop-order/below-null-preserved" 1 #[.null, intV 7, intV 5],
    mkShiftStackCase "/ok/pop-order/below-cell-preserved" 256 #[.cell Cell.empty, intV (-1), intV 1],
    mkShiftStackCase "/overflow/max-times-max-shift255" 255 #[intV maxInt257, intV maxInt257],
    mkShiftStackCase "/overflow/min-times-min-shift255" 255 #[intV minInt257, intV minInt257],
    mkShiftStackCase "/underflow/empty-stack" 1 #[],
    mkShiftStackCase "/underflow/one-arg" 1 #[intV 1],
    mkShiftStackCase "/error-order/underflow-before-type-one-non-int" 1 #[.null],
    mkShiftStackCase "/type/pop-y-first-non-int" 1 #[intV 1, .null],
    mkShiftStackCase "/type/pop-x-second-non-int" 1 #[.null, intV 1],
    mkShiftStackCase "/error-order/pop-y-before-x-both-non-int" 1 #[.null, .cell Cell.empty],
    mkRuntimeShiftCase "/error-order/range257-before-pop-type-in-lowered-path" 257 #[intV 1, .null],
    mkShiftInputCase "/nan/x-via-program" 1 .nan (.num 5),
    mkShiftInputCase "/nan/y-via-program" 1 (.num 5) .nan,
    mkShiftInputCase "/range/program-x-out-of-range" 1 (.num (maxInt257 + 1)) (.num 5),
    mkShiftInputCase "/range/program-y-out-of-range" 1 (.num 5) (.num (minInt257 - 1)),
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num mulrshiftcHashSetGasExact), .tonEnvOp .setGasLimit, mulrshiftcHashGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 1]
      #[.pushInt (.num mulrshiftcHashSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulrshiftcHashGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020897
      count := 700
      gen := genMulrshiftcHashFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFTC_HASH
