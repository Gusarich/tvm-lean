import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFT_HASH

/-
RSHIFT# branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod false false 1 (-1) false (some z))` specialization)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate SHR family `0xa934..0xa936 ++ (z-1)`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, 24-bit hash-immediate decode path for RSHIFT#/RSHIFTR#/RSHIFTC#)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, underflow/type behavior and non-quiet `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`mul=false`, `add=false`, `d=1`, `roundMode=-1`, `quiet=false`, `zOpt=some z`):
- Lean specialization: 6 branch sites / 8 terminal outcomes
  (dispatch/fallback; arity gate; `x` pop type/success; finite-vs-NaN split;
   invalid-int compat split (`shift ≤ 12` vs `≥ 13`) for `x=NaN`;
   non-quiet push result fit-vs-`intOv`).
- C++ specialization: 5 branch sites / 8 aligned terminal outcomes
  (underflow gate; `pop_int` type gate; finite-vs-invalid split; invalid-int
   compat split in `rshift_any`; `push_int_quiet` fit-vs-`int_ov`).

Key risk areas covered:
- hash-immediate discipline: shift is opcode-immediate and must not be popped;
- floor right-shift behavior across sign combinations and boundaries (`z=1`, `255`, `256`);
- strict arity/type ordering (`stkUnd` on empty stack before type paths);
- invalid-int compatibility for `x=NaN` with non-zero hash shift
  (`1..12 => 0`, `13..256 => -1`);
- non-serializable NaN/out-of-range injection only via prelude program (`PUSHINT`);
- exact gas cliff with `PUSHINT n; SETGASLIMIT; RSHIFT#` (exact success vs exact-1 OOG).
-/

private def rshiftHashId : InstrId := { name := "RSHIFT#" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkRshiftHashInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod false false 1 (-1) false (some shift))

private def rshiftHashInstrDefault : Instr :=
  mkRshiftHashInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[rshiftHashInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := rshiftHashId
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
  mkCase name stack #[mkRshiftHashInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkRshiftHashInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (progPrefix.push instr) gasLimits fuel

private def runRshiftHashDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkRshiftHashInstr shift) stack

private def runRshiftHashDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9721)) stack

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

private def rshiftHashGasProbeInstr : Instr :=
  mkRshiftHashInstr 13

private def rshiftHashSetGasExact : Int :=
  computeExactGasBudget rshiftHashGasProbeInstr

private def rshiftHashSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftHashGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 11, 12, 13, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def nanCompatShiftPool : Array Nat :=
  #[1, 2, 11, 12, 13, 64, 128, 256]

private def pickFromNatPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromNatPool shiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def pickNanCompatShift (rng : StdGen) : Nat × StdGen :=
  pickFromNatPool nanCompatShiftPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  (if pickCell then .cell Cell.empty else .null, rng')

private def classifyFiniteRshiftHash (x : Int) (shift : Nat) : String :=
  let q := floorDivPow2 x shift
  if intFitsSigned257 q then
    if q * intPow2 shift = x then "ok-exact" else "ok-inexact"
  else
    "intov-overflow"

private def classifyNanCompatRshiftHash (shift : Nat) : String :=
  if shift ≤ 12 then "ok-nan-compat-zero" else "ok-nan-compat-minus-one"

private def genRshiftHashFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyFiniteRshiftHash x shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/boundary-x-boundary-shift"
        shift #[intV x], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyFiniteRshiftHash x shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/signed-x-boundary-shift"
        shift #[intV x], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyFiniteRshiftHash x shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/boundary-x-random-shift"
        shift #[intV x], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyFiniteRshiftHash x shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/signed-x-random-shift"
        shift #[intV x], r3)
    else if shape = 4 then
      let (pickMin, r2) := randBool rng1
      let x := if pickMin then minInt257 else maxInt257
      let (shift, r3) := pickFromNatPool #[1, 12, 13, 255, 256] r2
      let kind := classifyFiniteRshiftHash x shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/extreme-boundary"
        shift #[intV x], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (below, r4) := pickNonInt r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/pop-order/immediate-does-not-pop-below"
        shift #[below, intV x], r4)
    else if shape = 6 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/empty-stack" shift #[], r2)
    else if shape = 7 then
      let (shift, r2) := pickShiftBoundary rng1
      let (xBad, r3) := pickNonInt r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/top-non-int"
        shift #[xBad], r3)
    else if shape = 8 then
      let (shift, r2) := pickNanCompatShift rng1
      let kind := classifyNanCompatRshiftHash shift
      (mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}/nan-via-program"
        shift #[.nan], r2)
    else if shape = 9 then
      let (shift, r2) := pickShiftInRange rng1
      let kind := classifyNanCompatRshiftHash shift
      (mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}/nan-via-program-random-shift"
        shift #[.nan], r2)
    else if shape = 10 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op"
        shift #[.num xOut], r3)
    else if shape = 11 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      let (below, r4) := pickNonInt r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-below-preserved"
        shift #[.num xOut] #[below], r4)
    else if shape = 12 then
      let (x, r2) := pickInt257Boundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/boundary/shift-1"
        1 #[intV x], r2)
    else if shape = 13 then
      let (x, r2) := pickInt257Boundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/boundary/shift-256"
        256 #[intV x], r2)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/ok/zero-input-fixed"
        256 #[intV (if x = 0 then 0 else x - x)], r2)
    else if shape = 15 then
      let (shift, r2) := pickShiftBoundary rng1
      let (xBad, r3) := pickNonInt r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/type-after-arity-gate"
        shift #[xBad], r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let q := floorDivPow2 x shift
      let alignedX := q * intPow2 shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/ok-exact/aligned-multiple"
        shift #[intV alignedX], r3)
    else
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-recheck"
        shift #[.num xOut], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := rshiftHashId
  unit := #[
    { name := "/unit/direct/floor-sign-zero-and-shift-invariants"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (0, 1, 0),
            (7, 1, 3),
            (7, 2, 1),
            (15, 3, 1),
            (-7, 1, -4),
            (-7, 2, -2),
            (-15, 3, -2),
            (1, 1, 0),
            (-1, 1, -1),
            (12345, 8, floorDivPow2 12345 8),
            (-12345, 8, floorDivPow2 (-12345) 8)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"/unit/direct/x={x}/z={shift}"
            (runRshiftHashDirect shift #[intV x]) #[intV expected] }
    ,
    { name := "/unit/direct/boundary-extremes-and-threshold-shifts"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (maxInt257, 1, (pow2 255) - 1),
            (minInt257, 1, -(pow2 255)),
            (maxInt257, 255, 1),
            (minInt257, 255, -2),
            (maxInt257, 256, 0),
            (maxInt257 - 1, 256, 0),
            (minInt257, 256, -1),
            (minInt257 + 1, 256, -1),
            (pow2 255, 256, 0),
            (-(pow2 255), 256, -1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"/unit/boundary/x={x}/z={shift}"
            (runRshiftHashDirect shift #[intV x]) #[intV expected] }
    ,
    { name := "/unit/pop-order/hash-immediate-does-not-pop-below"
      run := do
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runRshiftHashDirect 3 #[.null, intV 13]) #[.null, intV 1]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runRshiftHashDirect 2 #[.cell Cell.empty, intV (-13)]) #[.cell Cell.empty, intV (-4)] }
    ,
    { name := "/unit/error/underflow-type-and-error-order"
      run := do
        expectErr "/unit/error/underflow/empty-stack" (runRshiftHashDirect 1 #[]) .stkUnd
        expectErr "/unit/error/type/top-null" (runRshiftHashDirect 1 #[.null]) .typeChk
        expectErr "/unit/error/type/top-cell" (runRshiftHashDirect 1 #[.cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/hash-immediate-range-check"
      run := do
        expectAssembleErr "/unit/opcode/range/z0" [mkRshiftHashInstr 0] .rangeChk
        expectAssembleErr "/unit/opcode/range/z257" [mkRshiftHashInstr 257] .rangeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let i1 := mkRshiftHashInstr 1
        let i256 := mkRshiftHashInstr 256
        let program : Array Instr := #[i1, i256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"/unit/opcode/decode: assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/opcode/decode/rshift-hash-z1" s0 i1 24
        let s2 ← expectDecodeStep "/unit/opcode/decode/rshift-hash-z256" s1 i256 24
        let s3 ← expectDecodeStep "/unit/opcode/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/opcode/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-shrmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runRshiftHashDispatchFallback #[]) #[intV 9721] }
  ]
  oracle := #[
    mkShiftStackCase "/ok/floor/pos-shift1" 1 #[intV 7],
    mkShiftStackCase "/ok/floor/neg-shift1" 1 #[intV (-7)],
    mkShiftStackCase "/ok/floor/pos-shift2" 2 #[intV 7],
    mkShiftStackCase "/ok/floor/neg-shift2" 2 #[intV (-7)],
    mkShiftStackCase "/ok/floor/shift8-pos" 8 #[intV 12345],
    mkShiftStackCase "/ok/floor/shift8-neg" 8 #[intV (-12345)],
    mkShiftStackCase "/ok/floor/zero-input-shift256" 256 #[intV 0],
    mkShiftStackCase "/ok/boundary/max-shift1" 1 #[intV maxInt257],
    mkShiftStackCase "/ok/boundary/min-shift1" 1 #[intV minInt257],
    mkShiftStackCase "/ok/boundary/max-shift255" 255 #[intV maxInt257],
    mkShiftStackCase "/ok/boundary/min-shift255" 255 #[intV minInt257],
    mkShiftStackCase "/ok/boundary/max-shift256" 256 #[intV maxInt257],
    mkShiftStackCase "/ok/boundary/min-shift256" 256 #[intV minInt257],
    mkShiftStackCase "/ok/boundary/min-plus-one-shift256" 256 #[intV (minInt257 + 1)],
    mkShiftStackCase "/ok/boundary/max-minus-one-shift256" 256 #[intV (maxInt257 - 1)],
    mkShiftStackCase "/ok/pop-order/below-null-preserved" 3 #[.null, intV 13],
    mkShiftStackCase "/ok/pop-order/below-cell-preserved" 2 #[.cell Cell.empty, intV (-13)],
    mkShiftStackCase "/underflow/empty-stack" 1 #[],
    mkShiftStackCase "/error-order/underflow-before-type-empty-stack" 256 #[],
    mkShiftStackCase "/type/top-null" 1 #[.null],
    mkShiftStackCase "/type/top-cell" 1 #[.cell Cell.empty],
    mkShiftInputCase "/ok/nan-compat/shift1-zero-via-program" 1 #[.nan],
    mkShiftInputCase "/ok/nan-compat/shift12-zero-via-program" 12 #[.nan],
    mkShiftInputCase "/ok/nan-compat/shift13-minus-one-via-program" 13 #[.nan],
    mkShiftInputCase "/ok/nan-compat/shift256-minus-one-via-program" 256 #[.nan],
    mkShiftInputCase "/error-order/pushint-overflow-high-before-op" 1 #[.num (maxInt257 + 1)],
    mkShiftInputCase "/error-order/pushint-overflow-low-before-op" 1 #[.num (minInt257 - 1)],
    mkShiftInputCase "/error-order/pushint-overflow-before-op-with-below" 13
      #[.num (maxInt257 + 1)] #[.null],
    mkCase "/gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num rshiftHashSetGasExact), .tonEnvOp .setGasLimit, rshiftHashGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num rshiftHashSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftHashGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020881
      count := 700
      gen := genRshiftHashFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFT_HASH
