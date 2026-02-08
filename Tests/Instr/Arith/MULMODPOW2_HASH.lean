import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULMODPOW2_HASH

/-
MULMODPOW2# branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/MulShrModConst.lean`
    (`execInstrArithMulShrModConst`, `.mulShrModConst 2 (-1) z` specialization)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`modPow2Round`, floor remainder modulo `2^z`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, 24-bit hash-immediate family `0xa9b***` to `.mulShrModConst`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (encode routing for `.mulShrModConst` / `.shrMod ... (some z)` must stay aligned with decode)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, hash-immediate registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`d=2`, `roundMode=-1`, hash-immediate `z ∈ [1,256]`, `quiet=false`, `add=false`):
- Lean specialization: 5 branch sites / 7 terminal outcomes
  (dispatch/fallback; `y` pop underflow/type/success; `x` pop underflow/type/success;
   numeric-vs-NaN split; non-quiet result push success-vs-`intOv` NaN funnel).
- C++ specialization (`exec_mulshrmod`, mode `z_in_args=true`): 6 branch sites /
  8 aligned terminal outcomes
  (opcode/args validity gate; arity underflow gate; `y`/`x` pop type gates;
   global-v13 NaN funnel; non-quiet push success-vs-`int_ov`).

Key risk areas covered:
- hash-immediate discipline (`z` comes from opcode, never stack) and raw decode boundary
  powers (`z=1`, `z=255`, `z=256`);
- floor modulo behavior for all sign combinations and extreme 257-bit endpoints;
- strict pop/error ordering for a 2-operand op (`y` first, then `x`);
- underflow/type precedence and lower-stack preservation;
- NaN/out-of-range operands injected through program prelude only;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; MULMODPOW2#`.
-/

private def mulmodpow2HashId : InstrId := { name := "MULMODPOW2#" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkMulmodpow2HashInstr (shift : Nat) : Instr :=
  .mulShrModConst 2 (-1) shift

private def mulmodpow2HashInstrDefault : Instr :=
  mkMulmodpow2HashInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[mulmodpow2HashInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := mulmodpow2HashId
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
  mkCase name stack #[mkMulmodpow2HashInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkMulmodpow2HashInstr shift
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (programPrefix.push instr) gasLimits fuel

private def runMulmodpow2HashDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulShrModConst (mkMulmodpow2HashInstr shift) stack

private def runMulmodpow2HashDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithMulShrModConst .add (VM.push (intV 9482)) stack

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

private def expectDecodeErr
    (label : String)
    (s : Slice)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr {reprStr instr} ({bits} bits)")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")

private def mkMulmodpow2HashWord (shift : Nat) : Nat :=
  (0xa9b <<< 12) + (8 <<< 8) + (shift - 1)

private def mulmodpow2HashGasProbeInstr : Instr :=
  mkMulmodpow2HashInstr 7

private def mulmodpow2HashSetGasExact : Int :=
  computeExactGasBudget mulmodpow2HashGasProbeInstr

private def mulmodpow2HashSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne mulmodpow2HashGasProbeInstr

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def smallSignedPool : Array Int :=
  #[-33, -17, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 17, 33]

private def shift256XPool : Array Int :=
  #[minInt257, minInt257 + 1, -1, 0, 1, maxInt257 - 1, maxInt257]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 1 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  (if pickCell then .cell Cell.empty else .null, rng')

private def classifyMulmodpow2Hash (x y : Int) (shift : Nat) : String :=
  let r := modPow2Round (x * y) shift (-1)
  if r = 0 then "ok-exact" else "ok-inexact"

private def genMulmodpow2HashFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyMulmodpow2Hash x y shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-x-boundary-y-boundary-z"
        shift #[intV x, intV y], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyMulmodpow2Hash x y shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/signed-x-signed-y-random-z"
        shift #[intV x, intV y], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyMulmodpow2Hash x y shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/x-boundary"
        shift #[intV x, intV y], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyMulmodpow2Hash x y shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/y-boundary"
        shift #[intV x, intV y], r4)
    else if shape = 4 then
      let (x, r2) := pickFromPool smallSignedPool rng1
      let (y, r3) := pickFromPool smallSignedPool r2
      let (shift, r4) := pickFromPool (#[1, 2, 3, 4, 5, 6, 7, 8] : Array Nat) r3
      let kind := classifyMulmodpow2Hash x y shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/small-sign-mix"
        shift #[intV x, intV y], r4)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyMulmodpow2Hash x y 1
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift1"
        1 #[intV x, intV y], r3)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let kind := classifyMulmodpow2Hash x y 255
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift255"
        255 #[intV x, intV y], r3)
    else if shape = 7 then
      let (x, r2) := pickFromPool shift256XPool rng1
      let (y, r3) := pickFromPool smallSignedPool r2
      let kind := classifyMulmodpow2Hash x y 256
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift256"
        256 #[intV x, intV y], r3)
    else if shape = 8 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty" shift #[], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/one-int" shift #[intV x], r3)
    else if shape = 10 then
      let (bad, r2) := pickNonInt rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftCase s!"/fuzz/shape-{shape}/type/one-non-int" shift #[bad], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/pop-y-first" shift #[intV x, yLike], r4)
    else if shape = 12 then
      let (xLike, r2) := pickNonInt rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/pop-x-second" shift #[xLike, intV y], r4)
    else if shape = 13 then
      let (xLike, r2) := pickNonInt rng1
      let (yLike, r3) := pickNonInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-both-non-int"
        shift #[xLike, yLike], r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let (below, r5) := pickNonInt r4
      let kind := classifyMulmodpow2Hash x y shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/pop-order/below-preserved"
        shift #[below, intV x, intV y], r5)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-y-via-program"
        shift #[.num x, .nan], r3)
    else if shape = 16 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program"
        shift #[.nan, .num y], r3)
    else if shape = 17 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let (xOut, r4) := pickInt257OutOfRange r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        shift #[.num xOut, .num y], r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let (yOut, r4) := pickInt257OutOfRange r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        shift #[.num x, .num yOut], r4)
    else
      let (shift, r2) := pickShiftBoundary rng1
      let (xOut, r3) := pickInt257OutOfRange r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-and-before-typecheck"
        shift #[.num xOut, .num 7] #[.null], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := mulmodpow2HashId
  unit := #[
    { name := "/unit/direct/floor-modpow2-sign-and-boundary-invariants"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (7, 3, 1, 1),
            (-7, 3, 1, 1),
            (7, -3, 1, 1),
            (-7, -3, 1, 1),
            (7, 3, 2, 1),
            (-7, 3, 2, 3),
            (7, -3, 2, 3),
            (-7, -3, 2, 1),
            (13, 11, 4, 15),
            (-13, 11, 4, 1),
            (13, -11, 4, 1),
            (-13, -11, 4, 15),
            (5, 0, 7, 0),
            (0, 5, 7, 0),
            (maxInt257, 1, 1, 1),
            (maxInt257, 1, 255, (pow2 255) - 1),
            (maxInt257, 1, 256, maxInt257),
            (minInt257, 1, 1, 0),
            (minInt257, 1, 255, 0),
            (minInt257, 1, 256, 0),
            (minInt257 + 1, -1, 256, maxInt257),
            (-1, 1, 256, maxInt257)
          ]
        for c in checks do
          match c with
          | (x, y, shift, expected) =>
              expectOkStack s!"/unit/direct/x={x}/y={y}/z={shift}"
                (runMulmodpow2HashDirect shift #[intV x, intV y]) #[intV expected] }
    ,
    { name := "/unit/pop-order/lower-stack-preservation"
      run := do
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runMulmodpow2HashDirect 4 #[.null, intV 13, intV 11]) #[.null, intV 15]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runMulmodpow2HashDirect 2 #[.cell Cell.empty, intV (-13), intV 11]) #[.cell Cell.empty, intV 1] }
    ,
    { name := "/unit/error/underflow-type-and-pop-ordering"
      run := do
        expectErr "/unit/error/underflow-empty" (runMulmodpow2HashDirect 1 #[]) .stkUnd
        expectErr "/unit/error/underflow-one-int" (runMulmodpow2HashDirect 1 #[intV 7]) .stkUnd
        expectErr "/unit/error/type-one-non-int-null" (runMulmodpow2HashDirect 1 #[.null]) .typeChk
        expectErr "/unit/error/type-one-non-int-cell" (runMulmodpow2HashDirect 1 #[.cell Cell.empty]) .typeChk
        expectErr "/unit/error/type-pop-y-first"
          (runMulmodpow2HashDirect 4 #[intV 7, .null]) .typeChk
        expectErr "/unit/error/type-pop-x-second"
          (runMulmodpow2HashDirect 4 #[.null, intV 7]) .typeChk
        expectErr "/unit/error/order-pop-y-before-x-when-both-non-int"
          (runMulmodpow2HashDirect 4 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/hash-immediate-decode-and-routing"
      run := do
        expectAssembleErr "/unit/opcode/encode/arithExt-route-rangechk-z0"
          [.arithExt (.shrMod true false 2 (-1) false (some 0))] .rangeChk
        expectAssembleErr "/unit/opcode/encode/arithExt-route-invopcode-z1"
          [.arithExt (.shrMod true false 2 (-1) false (some 1))] .invOpcode
        let instr1 := mkMulmodpow2HashInstr 1
        let instr256 := mkMulmodpow2HashInstr 256
        let bits : BitString :=
          natToBits (mkMulmodpow2HashWord 1) 24 ++
          natToBits (mkMulmodpow2HashWord 256) 24 ++
          natToBits 0xa0 8
        let code := Cell.mkOrdinary bits #[]
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/opcode/decode/mulmodpow2-hash-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/opcode/decode/mulmodpow2-hash-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/opcode/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/opcode/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining")
        let badWordD0 : Nat := (0xa9b <<< 12) + (0 <<< 8)
        let badCellD0 := Cell.mkOrdinary (natToBits badWordD0 24) #[]
        let _ ← expectDecodeStep "/unit/opcode/decode/d-zero-routes-to-other-hash-op"
          (Slice.ofCell badCellD0)
          (.arithExt (.shrMod true true 3 (-1) false (some 1)))
          24
        pure () }
    ,
    { name := "/unit/dispatch/non-mulshrmodconst-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runMulmodpow2HashDispatchFallback #[]) #[intV 9482] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/floor/shift1/pos-pos" 1 #[.num 7, .num 3],
    mkShiftInputCase "/ok/floor/shift1/neg-pos" 1 #[.num (-7), .num 3],
    mkShiftInputCase "/ok/floor/shift1/pos-neg" 1 #[.num 7, .num (-3)],
    mkShiftInputCase "/ok/floor/shift1/neg-neg" 1 #[.num (-7), .num (-3)],
    mkShiftInputCase "/ok/floor/shift2/pos-pos-inexact" 2 #[.num 7, .num 3],
    mkShiftInputCase "/ok/floor/shift2/neg-pos-inexact" 2 #[.num (-7), .num 3],
    mkShiftInputCase "/ok/floor/shift2/pos-neg-inexact" 2 #[.num 7, .num (-3)],
    mkShiftInputCase "/ok/floor/shift2/neg-neg-inexact" 2 #[.num (-7), .num (-3)],
    mkShiftInputCase "/ok/exact/zero-left-factor" 7 #[.num 0, .num 19],
    mkShiftInputCase "/ok/exact/zero-right-factor" 7 #[.num 19, .num 0],
    mkShiftInputCase "/ok/boundary/shift1-max-times-one" 1 #[.num maxInt257, .num 1],
    mkShiftInputCase "/ok/boundary/shift1-min-times-one" 1 #[.num minInt257, .num 1],
    mkShiftInputCase "/ok/boundary/shift255-max-times-one" 255 #[.num maxInt257, .num 1],
    mkShiftInputCase "/ok/boundary/shift255-min-times-one" 255 #[.num minInt257, .num 1],
    mkShiftInputCase "/ok/boundary/shift256-max-times-one" 256 #[.num maxInt257, .num 1],
    mkShiftInputCase "/ok/boundary/shift256-min-times-one" 256 #[.num minInt257, .num 1],
    mkShiftInputCase "/ok/boundary/shift256-min-plus-one-times-negone"
      256 #[.num (minInt257 + 1), .num (-1)],
    mkShiftInputCase "/ok/boundary/shift256-negone-times-one" 256 #[.num (-1), .num 1],
    mkShiftCase "/ok/pop-order/below-null-preserved" 4 #[.null, intV 13, intV 11],
    mkShiftCase "/ok/pop-order/below-cell-preserved" 2 #[.cell Cell.empty, intV (-13), intV 11],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/underflow/one-int" 1 #[intV 7],
    mkShiftCase "/type/one-non-int-null" 1 #[.null],
    mkShiftCase "/type/one-non-int-cell" 1 #[.cell Cell.empty],
    mkShiftCase "/type/pop-y-first-null" 4 #[intV 7, .null],
    mkShiftCase "/type/pop-x-second-null" 4 #[.null, intV 7],
    mkShiftCase "/error-order/pop-y-before-x-when-both-non-int" 4 #[.null, .cell Cell.empty],
    mkShiftInputCase "/intov/nan-y-via-program" 7 #[.num 7, .nan],
    mkShiftInputCase "/intov/nan-x-via-program" 7 #[.nan, .num 7],
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op-pos" 7 #[.num (pow2 256), .num 7],
    mkShiftInputCase "/error-order/pushint-overflow-y-before-op-pos" 7 #[.num 7, .num (pow2 256)],
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op-neg"
      7 #[.num (-(pow2 256) - 1), .num 7],
    mkShiftInputCase "/error-order/pushint-overflow-before-op-and-before-typecheck"
      7 #[.num (pow2 256), .num 7] #[.null],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num mulmodpow2HashSetGasExact), .tonEnvOp .setGasLimit, mulmodpow2HashGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num mulmodpow2HashSetGasExactMinusOne), .tonEnvOp .setGasLimit, mulmodpow2HashGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020819
      count := 700
      gen := genMulmodpow2HashFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULMODPOW2_HASH
