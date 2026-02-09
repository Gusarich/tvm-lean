import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULRSHIFT_HASH

/-
MULRSHIFT# branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulShrModConst.lean`
    (`execInstrArithMulShrModConst`, `.mulShrModConst 1 (-1) z` specialization)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type/overflow behavior)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, floor right-shift semantics)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, `0xa9b` hash-immediate mul-shr decode family)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeCp0`, `0xa9b` hash-immediate mul-shr encode family with `z ∈ [1,256]`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, non-quiet `push_int_quiet`)

Branch/terminal counts used for this suite
(`d=1`, `roundMode=-1`, `z∈[1,256]`, non-quiet hash-immediate path):
- Lean specialization: ~6 branch sites / ~9 terminal outcomes
  (dispatch/fallback; `y` pop underflow/type; `x` pop underflow/type;
   finite-vs-NaN operand split; `d` arm; non-quiet push fit-vs-`intOv`).
- C++ specialization: ~6 branch sites / ~9 aligned terminal outcomes
  (`check_underflow(2)`; `pop_int` order `y→x`; finite-vs-invalid split;
   floor shift path; non-quiet push overflow/NaN funnel).

Key risk areas covered:
- hash-immediate discipline: `z` comes from opcode, so stack arity is exactly two inputs (`x`,`y`);
- floor product-shift invariants across signs and near-boundary values;
- boundary shifts (`1`, `255`, `256`) with signed-257 extremes;
- strict pop and error ordering (`y` before `x`, underflow/type precedence);
- NaN and out-of-range injection only via program prelude helper in oracle/fuzz;
- precision gas cliff (`SETGASLIMIT` exact vs exact-minus-one) using shared gas helpers.
-/

private def mulrshiftHashId : InstrId := { name := "MULRSHIFT#" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkMulrshiftHashInstr (shift : Nat) : Instr :=
  .mulShrModConst 1 (-1) shift

private def mulrshiftHashInstrDefault : Instr :=
  mkMulrshiftHashInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulrshiftHashInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := mulrshiftHashId
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
  mkCase name stack #[mkMulrshiftHashInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkMulrshiftHashInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (progPrefix.push instr) gasLimits fuel

private def runMulrshiftHashDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulShrModConst (mkMulrshiftHashInstr shift) stack

private def runMulrshiftHashDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulShrModConst .add (VM.push (intV 9642)) stack

private def expectAssembleErr (label : String) (instr : Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {e}")

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

private def mulrshiftHashGasProbeInstr : Instr :=
  mkMulrshiftHashInstr 7

private def mulrshiftHashSetGasExact : Int :=
  computeExactGasBudget mulrshiftHashGasProbeInstr

private def mulrshiftHashSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulrshiftHashGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def nearBoundaryFactorPool : Array Int :=
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

private def pickNearBoundaryFactor (rng : StdGen) : Int × StdGen :=
  pickFromPool nearBoundaryFactorPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def classifyMulrshiftHash (x : Int) (y : Int) (shift : Nat) : String :=
  let prod := x * y
  let q := floorDivPow2 prod shift
  if q * intPow2 shift = prod then
    "ok-exact"
  else if x = 0 ∨ y = 0 then
    "ok-zero-factor"
  else if shift = 256 then
    "ok-shift256"
  else if
      x = maxInt257 ∨ x = minInt257 ∨ x = maxInt257 - 1 ∨ x = minInt257 + 1 ∨
      y = maxInt257 ∨ y = minInt257 ∨ y = maxInt257 - 1 ∨ y = minInt257 + 1 then
    "ok-boundary-factor"
  else if prod < 0 then
    "ok-sign-neg"
  else
    "ok-sign-pos"

private def mkFiniteFuzzCase (shape : Nat) (x : Int) (y : Int) (shift : Nat) : OracleCase :=
  let kind := classifyMulrshiftHash x y shift
  mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}" shift #[intV x, intV y]

private def genMulrshiftHashFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
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
      let (shift, r4) := pickShiftMixed r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftMixed r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftMixed r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 4 then
      let (x, r2) := pickNearBoundaryFactor rng1
      let (y, r3) := pickNearBoundaryFactor r2
      let (shift, r4) := pickShiftBoundary r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 5 then
      let (x, r2) := pickNearBoundaryFactor rng1
      let (y, r3) := pickNearBoundaryFactor r2
      (mkFiniteFuzzCase shape x y 256, r3)
    else if shape = 6 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkFiniteFuzzCase shape 0 y shift, r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkFiniteFuzzCase shape x 0 shift, r3)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/pop-order/below-null-preserved"
        shift #[.null, intV x, intV y], r4)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/pop-order/below-cell-preserved"
        shift #[.cell Cell.empty, intV x, intV y], r4)
    else if shape = 10 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/empty-stack" shift #[], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/single-int" shift #[intV x], r3)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let (badY, r4) := pickNonInt r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/y-top-non-int"
        shift #[intV x, badY], r4)
    else if shape = 13 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let (badX, r4) := pickNonInt r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/x-second-non-int"
        shift #[badX, intV y], r4)
    else if shape = 14 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/y-before-x-when-both-non-int"
        shift #[.null, .cell Cell.empty], r2)
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
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-high-before-op"
        shift #[.num (maxInt257 + 1), .num y], r3)
    else if shape = 18 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-low-before-op"
        shift #[.num (minInt257 - 1), .num y], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-high-before-op"
        shift #[.num x, .num (maxInt257 + 1)], r3)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-low-before-op"
        shift #[.num x, .num (minInt257 - 1)], r3)
    else if shape = 21 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-type-check"
        #[.null] #[.pushInt (.num (pow2 257)), mkMulrshiftHashInstr shift], r2)
    else if shape = 22 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-underflow"
        #[] #[.pushInt (.num (-(pow2 257))), mkMulrshiftHashInstr shift], r2)
    else if shape = 23 then
      (mkShiftStackCase s!"/fuzz/shape-{shape}/intov/result-overflow-max-max-shift1"
        1 #[intV maxInt257, intV maxInt257], rng1)
    else
      (mkFiniteFuzzCase shape 0 0 1, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulrshiftHashId
  unit := #[
    { name := "/unit/direct/floor-product-shift-sign-and-boundary-invariants"
      run := do
        let checks : Array (Int × Int × Nat) :=
          #[
            (7, 5, 1),
            (-7, 5, 1),
            (7, -5, 1),
            (-7, -5, 1),
            (13, 11, 3),
            (-13, 11, 3),
            (maxInt257, 1, 1),
            (maxInt257, 1, 255),
            (maxInt257, 1, 256),
            (minInt257, 1, 255),
            (minInt257, 1, 256),
            (maxInt257, -1, 256),
            (minInt257, -1, 256),
            (minInt257 + 1, -1, 256),
            (0, maxInt257, 128),
            (-1, 1, 256)
          ]
        for c in checks do
          match c with
          | (x, y, shift) =>
              let expected := floorDivPow2 (x * y) shift
              expectOkStack s!"/unit/direct/x={x}/y={y}/z={shift}"
                (runMulrshiftHashDirect shift #[intV x, intV y]) #[intV expected] }
    ,
    { name := "/unit/pop-order/hash-immediate-does-not-pop-below-items"
      run := do
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runMulrshiftHashDirect 3 #[.null, intV 13, intV 11])
          #[.null, intV (floorDivPow2 (13 * 11) 3)]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runMulrshiftHashDirect 2 #[.cell Cell.empty, intV (-13), intV 11])
          #[.cell Cell.empty, intV (floorDivPow2 ((-13) * 11) 2)]
        expectOkStack "/unit/pop-order/below-int-preserved"
          (runMulrshiftHashDirect 1 #[intV 99, intV (-7), intV 5])
          #[intV 99, intV (floorDivPow2 ((-7) * 5) 1)] }
    ,
    { name := "/unit/error/underflow-type-and-y-before-x-ordering"
      run := do
        expectErr "/unit/error/underflow/empty-stack"
          (runMulrshiftHashDirect 1 #[]) .stkUnd
        expectErr "/unit/error/underflow/single-int"
          (runMulrshiftHashDirect 1 #[intV 7]) .stkUnd
        expectErr "/unit/error/type/single-non-int"
          (runMulrshiftHashDirect 1 #[.null]) .stkUnd
        expectErr "/unit/error/type/y-top-non-int-before-x"
          (runMulrshiftHashDirect 1 #[intV 7, .null]) .typeChk
        expectErr "/unit/error/type/x-second-non-int-after-y"
          (runMulrshiftHashDirect 1 #[.null, intV 7]) .typeChk
        expectErr "/unit/error-order/y-before-x-when-both-non-int"
          (runMulrshiftHashDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/error/intov-result-overflow-path"
      run := do
        expectErr "/unit/intov/max-max-shift1"
          (runMulrshiftHashDirect 1 #[intV maxInt257, intV maxInt257]) .intOv
        expectErr "/unit/intov/min-min-shift1"
          (runMulrshiftHashDirect 1 #[intV minInt257, intV minInt257]) .intOv
        expectErr "/unit/intov/min-max-shift1"
          (runMulrshiftHashDirect 1 #[intV minInt257, intV maxInt257]) .intOv }
    ,
    { name := "/unit/opcode/hash-immediate-encode-decode-and-range"
      run := do
        expectAssembleErr "/unit/opcode/encode/z0-rangechk"
          (mkMulrshiftHashInstr 0) .rangeChk
        expectAssembleErr "/unit/opcode/encode/z257-rangechk"
          (mkMulrshiftHashInstr 257) .rangeChk
        let instr1 := mkMulrshiftHashInstr 1
        let instr256 := mkMulrshiftHashInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"/unit/opcode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/opcode/decode/mulrshift-hash-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/opcode/decode/mulrshift-hash-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/opcode/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/opcode/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-mulrshift-hash-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runMulrshiftHashDispatchFallback #[]) #[intV 9642] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/floor/sign/pos-pos-shift1" 1 #[.num 7, .num 5],
    mkShiftInputCase "/ok/floor/sign/neg-pos-shift1" 1 #[.num (-7), .num 5],
    mkShiftInputCase "/ok/floor/sign/pos-neg-shift1" 1 #[.num 7, .num (-5)],
    mkShiftInputCase "/ok/floor/sign/neg-neg-shift1" 1 #[.num (-7), .num (-5)],
    mkShiftInputCase "/ok/floor/nontrivial-shift3-pos" 3 #[.num 13, .num 11],
    mkShiftInputCase "/ok/floor/nontrivial-shift3-neg" 3 #[.num (-13), .num 11],
    mkShiftInputCase "/ok/floor/zero-left-factor" 17 #[.num 0, .num 12345],
    mkShiftInputCase "/ok/floor/zero-right-factor" 17 #[.num 12345, .num 0],
    mkShiftInputCase "/ok/boundary/max-times-one-shift1" 1 #[.num maxInt257, .num 1],
    mkShiftInputCase "/ok/boundary/max-times-one-shift255" 255 #[.num maxInt257, .num 1],
    mkShiftInputCase "/ok/boundary/max-times-one-shift256" 256 #[.num maxInt257, .num 1],
    mkShiftInputCase "/ok/boundary/min-times-one-shift255" 255 #[.num minInt257, .num 1],
    mkShiftInputCase "/ok/boundary/min-times-one-shift256" 256 #[.num minInt257, .num 1],
    mkShiftInputCase "/ok/boundary/max-times-negone-shift256" 256 #[.num maxInt257, .num (-1)],
    mkShiftInputCase "/ok/boundary/min-times-negone-shift256" 256 #[.num minInt257, .num (-1)],
    mkShiftInputCase "/ok/boundary/min-plus-one-times-negone-shift256" 256 #[.num (minInt257 + 1), .num (-1)],
    mkShiftStackCase "/ok/pop-order/below-null-preserved" 3 #[.null, intV 13, intV 11],
    mkShiftStackCase "/ok/pop-order/below-cell-preserved" 2 #[.cell Cell.empty, intV (-13), intV 11],
    mkShiftStackCase "/ok/pop-order/below-int-preserved" 1 #[intV 99, intV (-7), intV 5],
    mkShiftStackCase "/underflow/empty-stack" 1 #[],
    mkShiftStackCase "/underflow/single-int" 1 #[intV 7],
    mkShiftStackCase "/type/single-non-int" 1 #[.null],
    mkShiftStackCase "/type/y-top-non-int-before-x" 1 #[intV 7, .null],
    mkShiftStackCase "/type/x-second-non-int-after-y" 1 #[.null, intV 7],
    mkShiftStackCase "/error-order/y-before-x-when-both-non-int" 1 #[.null, .cell Cell.empty],
    mkShiftInputCase "/intov/nan-x-via-program-shift1" 1 #[.nan, .num 5],
    mkShiftInputCase "/intov/nan-y-via-program-shift1" 1 #[.num 7, .nan],
    mkShiftInputCase "/intov/nan-x-via-program-shift256" 256 #[.nan, .num 1],
    mkShiftInputCase "/intov/nan-y-via-program-shift256" 256 #[.num 1, .nan],
    mkShiftInputCase "/error-order/pushint-overflow-x-high-before-op" 1 #[.num (maxInt257 + 1), .num 5],
    mkShiftInputCase "/error-order/pushint-overflow-x-low-before-op" 1 #[.num (minInt257 - 1), .num 5],
    mkShiftInputCase "/error-order/pushint-overflow-y-high-before-op" 1 #[.num 5, .num (maxInt257 + 1)],
    mkShiftInputCase "/error-order/pushint-overflow-y-low-before-op" 1 #[.num 5, .num (minInt257 - 1)],
    mkCase "/error-order/pushint-overflow-before-op-type-check" #[.null]
      #[.pushInt (.num (pow2 257)), mkMulrshiftHashInstr 1],
    mkCase "/error-order/pushint-overflow-before-op-underflow" #[]
      #[.pushInt (.num (-(pow2 257))), mkMulrshiftHashInstr 1],
    mkShiftInputCase "/intov/result-overflow-max-max-shift1" 1 #[.num maxInt257, .num maxInt257],
    mkShiftInputCase "/intov/result-overflow-min-min-shift1" 1 #[.num minInt257, .num minInt257],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num mulrshiftHashSetGasExact), .tonEnvOp .setGasLimit, mulrshiftHashGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num mulrshiftHashSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulrshiftHashGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020895
      count := 700
      gen := genMulrshiftHashFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFT_HASH
