import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFTC_HASH

/-
RSHIFTC# branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod false false 1 1 false (some z))`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate SHR family `0xa934..0xa936`, `z ∈ [1, 256]`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, 24-bit hash-immediate decode for `.shrMod false false 1`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`, underflow/type/overflow behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`mul=false`, `add=false`, `d=1`, `roundMode=1`, `quiet=false`, `zOpt=some z`):
- `TvmLean/Semantics/Exec/Arith/Ext.lean`: 6 branch sites / 8 terminal outcomes
  (dispatch/fallback; depth gate; `x` pop type; finite-vs-NaN split; finite push fit-vs-`intOv`;
   NaN-compat push path).
- `TvmLean/Model/Instr/Asm/Cp0.lean`: 4 branch sites / 6 outcomes
  (round-mode offset; opcode-base selection; quiet-hash rejection; `z` range gate).
- `TvmLean/Model/Instr/Codepage/Cp0.lean`: 2 branch sites / 3 outcomes
  (`0xa934..0xa936` family match; round-offset decode; `z := arg8 + 1` extraction).
- C++ (`arithops.cpp` + `stack.cpp`): 6 branch sites / 8 aligned terminal outcomes
  (`check_underflow(1)`; const-shift decode route; `pop_int` type gate; numeric-vs-invalid split;
   ceil-rshift evaluation; non-quiet push funnel).

Key risk areas covered:
- hash-immediate semantics: shift comes from opcode, so single-item stacks are valid;
- ceil rounding/sign-extension at `z=1`, `z=255`, `z=256` near `±2^255` and `±2^256`;
- strict error ordering (`stkUnd` only on empty; non-empty non-int is `typeChk`);
- NaN compatibility (`x=NaN`, `z>0` yields `0`) and non-quiet overflow funnel on huge numerics;
- oracle/fuzz serialization hygiene: NaN/out-of-range values injected via `PUSHINT` prelude only;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; RSHIFTC#`.
-/

private def rshiftcHashId : InstrId := { name := "RSHIFTC#" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkRshiftcHashInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod false false 1 1 false (some shift))

private def rshiftcHashInstrDefault : Instr :=
  mkRshiftcHashInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[rshiftcHashInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := rshiftcHashId
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
  mkCase name stack #[mkRshiftcHashInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (x : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkRshiftcHashInstr shift
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stack) (programPrefix.push instr) gasLimits fuel

private def runRshiftcHashDirect (shift : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkRshiftcHashInstr shift) stack

private def runRshiftcHashDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9318)) stack

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

private def rshiftcHashGasProbeInstr : Instr :=
  mkRshiftcHashInstr 7

private def rshiftcHashSetGasExact : Int :=
  computeExactGasBudget rshiftcHashGasProbeInstr

private def rshiftcHashSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftcHashGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tinyShiftPool : Array Nat :=
  #[1, 2, 3, 4, 5, 6, 7, 8]

private def smallSignedPool : Array Int :=
  #[-33, -17, -13, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 13, 17, 33]

private def pickIntFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNatFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickNatFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 1 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def classifyRshiftcHash (x : Int) (shift : Nat) : String :=
  let q := rshiftPow2Round x shift 1
  if q * intPow2 shift = x then "ok-exact" else "ok-inexact"

private def genRshiftcHashFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyRshiftcHash x shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/x-boundary-shift-boundary" shift #[intV x], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyRshiftcHash x shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/x-random-shift-boundary" shift #[intV x], r3)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyRshiftcHash x shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/x-boundary-shift-inrange" shift #[intV x], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyRshiftcHash x shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/x-random-shift-inrange" shift #[intV x], r3)
    else if shape = 4 then
      let (x, r2) := pickIntFromPool smallSignedPool rng1
      let (shift, r3) := pickNatFromPool tinyShiftPool r2
      let kind := classifyRshiftcHash x shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/small-x-small-shift" shift #[intV x], r3)
    else if shape = 5 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/ok-exact/x-zero" shift #[intV 0], r2)
    else if shape = 6 then
      let (useMin, r2) := randBool rng1
      let x := if useMin then minInt257 else maxInt257
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyRshiftcHash x shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/x-extreme" shift #[intV x], r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/hash-immediate/single-item-valid" shift #[intV x], r3)
    else if shape = 8 then
      let (x, r2) := pickIntFromPool smallSignedPool rng1
      let (shift, r3) := pickNatFromPool tinyShiftPool r2
      let (below, r4) := pickNonInt r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/hash-immediate/below-preserved" shift #[below, intV x], r4)
    else if shape = 9 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/empty-stack" shift #[], r2)
    else if shape = 10 then
      let (shift, r2) := pickShiftBoundary rng1
      let (xLike, r3) := pickNonInt r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/single-non-int" shift #[xLike], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (xLike, r4) := pickNonInt r3
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/top-non-int-with-below-int"
        shift #[intV x, xLike], r4)
    else if shape = 12 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/x-via-program" shift .nan, r2)
    else if shape = 13 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-high-before-op"
        shift (.num (maxInt257 + 1)), r2)
    else if shape = 14 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-low-before-op"
        shift (.num (minInt257 - 1)), r2)
    else if shape = 15 then
      let (x, r2) := pickInt257Boundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/boundary/shift-256" 256 #[intV x], r2)
    else if shape = 16 then
      let (x, r2) := pickInt257Boundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/boundary/shift-1" 1 #[intV x], r2)
    else if shape = 17 then
      let (q, r2) := pickIntFromPool smallSignedPool rng1
      let (shift, r3) := pickNatFromPool tinyShiftPool r2
      let x := q * intPow2 shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/ok-exact/constructed-divisible" shift #[intV x], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/hash-immediate/below-int-preserved"
        shift #[intV 99, intV x], r3)
    else
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyRshiftcHash x shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/fallback" shift #[intV x], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := rshiftcHashId
  unit := #[
    { name := "/unit/direct/ceil-rounding-sign-and-boundary-cases"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (7, 1, 4),
            (7, 2, 2),
            (-7, 1, -3),
            (-7, 2, -1),
            (-15, 3, -1),
            (-1, 1, 0),
            (1, 1, 1),
            (maxInt257, 1, pow2 255),
            (minInt257, 1, -(pow2 255)),
            (maxInt257, 256, 1),
            (minInt257, 256, -1),
            (pow2 255, 256, 1),
            (-(pow2 255), 256, 0)
          ]
        for c in checks do
          match c with
          | (x, shift, expected) =>
              expectOkStack s!"/unit/direct/x={x}/z={shift}"
                (runRshiftcHashDirect shift #[intV x]) #[intV expected] }
    ,
    { name := "/unit/direct/hash-immediate-stack-behavior"
      run := do
        expectOkStack "/unit/hash-immediate/single-item-valid"
          (runRshiftcHashDirect 1 #[intV 7]) #[intV 4]
        expectOkStack "/unit/hash-immediate/below-int-preserved"
          (runRshiftcHashDirect 1 #[intV 99, intV 7]) #[intV 99, intV 4]
        expectOkStack "/unit/hash-immediate/below-null-preserved"
          (runRshiftcHashDirect 256 #[.null, intV (-1)]) #[.null, intV 0] }
    ,
    { name := "/unit/direct/nan-and-overflow-paths"
      run := do
        expectOkStack "/unit/nan/x-shift1-yields-zero"
          (runRshiftcHashDirect 1 #[.int .nan]) #[intV 0]
        expectOkStack "/unit/nan/x-shift256-yields-zero"
          (runRshiftcHashDirect 256 #[.int .nan]) #[intV 0]
        expectErr "/unit/intov/huge-positive-input"
          (runRshiftcHashDirect 1 #[intV (pow2 300)]) .intOv
        expectErr "/unit/intov/huge-negative-input"
          (runRshiftcHashDirect 1 #[intV (-(pow2 300))]) .intOv }
    ,
    { name := "/unit/error/underflow-type-and-ordering"
      run := do
        expectErr "/unit/underflow/empty-stack"
          (runRshiftcHashDirect 1 #[]) .stkUnd
        expectErr "/unit/type/single-null"
          (runRshiftcHashDirect 1 #[.null]) .typeChk
        expectErr "/unit/type/single-cell"
          (runRshiftcHashDirect 1 #[.cell Cell.empty]) .typeChk
        expectErr "/unit/type/top-null-with-below-int"
          (runRshiftcHashDirect 1 #[intV 7, .null]) .typeChk
        expectErr "/unit/type/top-cell-with-below-int"
          (runRshiftcHashDirect 1 #[intV 7, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkRshiftcHashInstr 1
        let instr256 := mkRshiftcHashInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/decode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/rshiftc-hash-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/rshiftc-hash-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/opcode/encode-invalid-immediate-range"
      run := do
        expectAssembleErr "/unit/encode/range/shift0" [mkRshiftcHashInstr 0] .rangeChk
        expectAssembleErr "/unit/encode/range/shift257" [mkRshiftcHashInstr 257] .rangeChk }
    ,
    { name := "/unit/dispatch/non-rshiftc-hash-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runRshiftcHashDispatchFallback #[]) #[intV 9318] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/ceil/sign/pos-shift1" 1 (.num 7),
    mkShiftInputCase "/ok/ceil/sign/neg-shift1" 1 (.num (-7)),
    mkShiftInputCase "/ok/ceil/sign/pos-shift2" 2 (.num 7),
    mkShiftInputCase "/ok/ceil/sign/neg-shift2" 2 (.num (-7)),
    mkShiftInputCase "/ok/ceil/tie/neg-half-to-zero" 1 (.num (-1)),
    mkShiftInputCase "/ok/ceil/tie/pos-half-to-one" 1 (.num 1),
    mkShiftInputCase "/ok/ceil/nontrivial-shift17" 17 (.num ((pow2 40) + 1)),
    mkShiftInputCase "/ok/ceil/zero-input-high-shift" 256 (.num 0),
    mkShiftInputCase "/ok/boundary/max-shift1" 1 (.num maxInt257),
    mkShiftInputCase "/ok/boundary/min-shift1" 1 (.num minInt257),
    mkShiftInputCase "/ok/boundary/max-shift256" 256 (.num maxInt257),
    mkShiftInputCase "/ok/boundary/min-shift256" 256 (.num minInt257),
    mkShiftInputCase "/ok/boundary/half-pos-at-2^255" 256 (.num (pow2 255)),
    mkShiftInputCase "/ok/boundary/half-neg-at-2^255" 256 (.num (-(pow2 255))),
    mkShiftStackCase "/ok/hash-immediate/single-item-no-runtime-shift-pop" 1 #[intV 7],
    mkShiftStackCase "/ok/hash-immediate/below-int-preserved" 1 #[intV 99, intV 7],
    mkShiftStackCase "/ok/hash-immediate/below-null-preserved" 256 #[.null, intV (-1)],
    mkShiftStackCase "/underflow/empty-stack" 1 #[],
    mkShiftStackCase "/type/single-null" 1 #[.null],
    mkShiftStackCase "/type/single-cell" 1 #[.cell Cell.empty],
    mkShiftStackCase "/type/top-null-with-below-int" 1 #[intV 7, .null],
    mkShiftStackCase "/type/top-cell-with-below-int" 1 #[intV 7, .cell Cell.empty],
    mkShiftInputCase "/nan/x-via-program-shift1-yields-zero" 1 .nan,
    mkShiftInputCase "/nan/x-via-program-shift256-yields-zero" 256 .nan,
    mkShiftInputCase "/error-order/pushint-overflow-x-high-before-op" 1 (.num (maxInt257 + 1)),
    mkShiftInputCase "/error-order/pushint-overflow-x-low-before-op" 1 (.num (minInt257 - 1)),
    mkCase "/gas/exact-cost-succeeds" #[intV 13]
      #[.pushInt (.num rshiftcHashSetGasExact), .tonEnvOp .setGasLimit, rshiftcHashGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 13]
      #[.pushInt (.num rshiftcHashSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftcHashGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020893
      count := 700
      gen := genRshiftcHashFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFTC_HASH
