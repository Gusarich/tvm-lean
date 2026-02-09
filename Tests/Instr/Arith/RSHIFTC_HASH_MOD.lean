import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFTC_HASH_MOD

/-
RSHIFTC#MOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false false 3 1 false (some z)` specialization)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type/overflow behavior)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, `modPow2Round`, ceil quotient/remainder invariants)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (hash-immediate encode checks for `z ∈ [1, 256]`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (hash-immediate decode family for `RSHIFTC#MOD`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, opcode registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, non-quiet `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::rshift_any`, `AnyIntView::mod_pow2_any`)

Branch/terminal counts used for this suite (`mul=false`, `add=false`, `d=3`,
`roundMode=1`, `quiet=false`, `zOpt=some z`):
- Lean specialization: ~6 branch sites / ~8 terminal outcomes
  (dispatch/fallback; underflow gate; single-pop `x` type split; ceil-mode
   numeric-vs-NaN split; `d=3` dual-result push with non-quiet overflow funnel).
- C++ specialization: ~6 branch sites / ~8 aligned terminal outcomes
  (invalid-opcode guard; `check_underflow(1)`; `pop_int` type split; ceil
   rounding path; `RSHIFTMOD` two-result route; non-quiet push overflow funnel).

Key risk areas covered:
- ceil quotient/remainder correctness for mixed signs and ties;
- boundary shifts (`1`, `255`, `256`) with signed-257 extremes;
- strict pop/error ordering (underflow before type; top-of-stack consumed first);
- hash-immediate codec boundaries (`z=0` / `z=257` rejected by assembler);
- NaN and out-of-range integer injection only via program prelude helper;
- precision gas cliff (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def rshiftcHashModId : InstrId := { name := "RSHIFTC#MOD" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkRshiftcHashModInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod false false 3 1 false (some shift))

private def rshiftcHashModGasProbeInstr : Instr :=
  mkRshiftcHashModInstr 7

private def rshiftcHashModGasProbeInstr256 : Instr :=
  mkRshiftcHashModInstr 256

private def rshiftcHashModSetGasExact : Int :=
  computeExactGasBudget rshiftcHashModGasProbeInstr

private def rshiftcHashModSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftcHashModGasProbeInstr

private def rshiftcHashModSetGasExact256 : Int :=
  computeExactGasBudget rshiftcHashModGasProbeInstr256

private def rshiftcHashModSetGasExactMinusOne256 : Int :=
  computeExactGasBudgetMinusOne rshiftcHashModGasProbeInstr256

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := rshiftcHashModId
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
  mkCase name stack #[mkRshiftcHashModInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkRshiftcHashModInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (progPrefix.push instr) gasLimits fuel

private def runRshiftcHashModDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkRshiftcHashModInstr shift) stack

private def runRshiftcHashModDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 8452)) stack

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error err =>
      throw (IO.userError s!"{label}: decode failed with {err}")
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
  | .error err =>
      if err = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {err}")

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tinyShiftPool : Array Nat :=
  #[1, 2, 3, 4, 5, 6, 7, 8]

private def nearBoundaryXPool : Array Int :=
  #[-33, -17, -13, -9, -7, -5, -3, -2, -1, 0, 1, 2, 3, 5, 7, 9, 13, 17, 33]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 1 256

private def pickTinyShift (rng : StdGen) : Nat × StdGen :=
  pickFromPool tinyShiftPool rng

private def pickNearBoundaryX (rng : StdGen) : Int × StdGen :=
  pickFromPool nearBoundaryXPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def classifyRshiftcHashMod (x : Int) (shift : Nat) : String :=
  let r := modPow2Round x shift 1
  if r = 0 then
    "ok-exact"
  else if x = 0 ∨ x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 then
    "ok-near-boundary"
  else if x = maxInt257 ∨ x = minInt257 ∨ x = maxInt257 - 1 ∨ x = minInt257 + 1 then
    "ok-boundary"
  else if shift = 256 then
    "ok-shift256"
  else if x < 0 then
    "ok-sign-neg"
  else
    "ok-sign-pos"

private def mkFiniteFuzzCase (shape : Nat) (x : Int) (shift : Nat) : OracleCase :=
  let kind := classifyRshiftcHashMod x shift
  mkShiftCase s!"/fuzz/shape-{shape}/{kind}" shift #[intV x]

private def genRshiftcHashModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 23
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkFiniteFuzzCase shape x shift, r3)
    else if shape = 1 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftMixed r2
      (mkFiniteFuzzCase shape x shift, r3)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkFiniteFuzzCase shape x shift, r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftMixed r2
      (mkFiniteFuzzCase shape x shift, r3)
    else if shape = 4 then
      let (x, r2) := pickNearBoundaryX rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkFiniteFuzzCase shape x shift, r3)
    else if shape = 5 then
      let (x, r2) := pickNearBoundaryX rng1
      (mkFiniteFuzzCase shape x 256, r2)
    else if shape = 6 then
      let (shift, r2) := pickShiftMixed rng1
      (mkFiniteFuzzCase shape 0 shift, r2)
    else if shape = 7 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty-stack" shift #[], r2)
    else if shape = 8 then
      let (shift, r2) := pickShiftBoundary rng1
      let (badTop, r3) := pickNonInt r2
      (mkShiftCase s!"/fuzz/shape-{shape}/type/top-non-int" shift #[badTop], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let (below, r4) := pickNonInt r3
      (mkShiftCase s!"/fuzz/shape-{shape}/pop-order/below-preserved"
        shift #[below, intV x], r4)
    else if shape = 10 then
      let (below, r2) := pickSigned257ish rng1
      let (badTop, r3) := pickNonInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/type-top-before-below-int"
        shift #[intV below, badTop], r4)
    else if shape = 11 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program-shift1"
        1 #[.nan], rng1)
    else if shape = 12 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program-shift256"
        256 #[.nan], rng1)
    else if shape = 13 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-high-before-op"
        shift #[.num (maxInt257 + 1)], r2)
    else if shape = 14 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-low-before-op"
        shift #[.num (minInt257 - 1)], r2)
    else if shape = 15 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-type-check"
        shift #[.num (pow2 257)] #[.null], r2)
    else if shape = 16 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-underflow"
        shift #[.num (-(pow2 257))], r2)
    else if shape = 17 then
      let (quotSeed, r2) := pickNearBoundaryX rng1
      let (shift, r3) := pickTinyShift r2
      let x := quotSeed * pow2 shift
      (mkFiniteFuzzCase shape x shift, r3)
    else if shape = 18 then
      let (quotSeed, r2) := pickNearBoundaryX rng1
      let (shift, r3) := pickTinyShift r2
      let x := -(Int.ofNat (Int.natAbs quotSeed)) * pow2 shift
      (mkFiniteFuzzCase shape x shift, r3)
    else if shape = 19 then
      (mkFiniteFuzzCase shape maxInt257 256, rng1)
    else if shape = 20 then
      (mkFiniteFuzzCase shape minInt257 256, rng1)
    else if shape = 21 then
      (mkFiniteFuzzCase shape 1 256, rng1)
    else if shape = 22 then
      (mkFiniteFuzzCase shape (-1) 256, rng1)
    else if shape = 23 then
      let (x, r2) := pickNearBoundaryX rng1
      (mkFiniteFuzzCase shape x 1, r2)
    else
      (mkFiniteFuzzCase shape 0 1, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := rshiftcHashModId
  unit := #[
    { name := "/unit/ok/ceil-quot-rem-sign-and-near-boundary-invariants"
      run := do
        let checks : Array (Int × Nat × Int × Int) :=
          #[
            (7, 1, 4, -1),
            (-7, 1, -3, -1),
            (7, 2, 2, -1),
            (-7, 2, -1, -3),
            (1, 1, 1, -1),
            (-1, 1, 0, -1),
            (3, 2, 1, -1),
            (-3, 2, 0, -3),
            (8, 3, 1, 0),
            (-8, 3, -1, 0),
            (9, 3, 2, -7),
            (-9, 3, -1, -1),
            (0, 16, 0, 0)
          ]
        for entry in checks do
          match entry with
          | (x, shift, q, r) =>
              expectOkStack s!"/unit/ok/x={x}/z={shift}"
                (runRshiftcHashModDirect shift #[intV x]) #[intV q, intV r] }
    ,
    { name := "/unit/boundary/shifts-and-signed257-extremes"
      run := do
        let checks : Array (Int × Nat × Int × Int) :=
          #[
            (maxInt257, 1, pow2 255, -1),
            (minInt257, 1, -(pow2 255), 0),
            (maxInt257, 255, 2, -1),
            (minInt257, 255, -2, 0),
            (maxInt257, 256, 1, -1),
            (maxInt257 - 1, 256, 1, -2),
            (minInt257, 256, -1, 0),
            (minInt257 + 1, 256, 0, minInt257 + 1),
            (1, 256, 1, minInt257 + 1),
            (-1, 256, 0, -1),
            (pow2 255, 256, 1, -(pow2 255)),
            (-(pow2 255), 256, 0, -(pow2 255))
          ]
        for entry in checks do
          match entry with
          | (x, shift, q, r) =>
              expectOkStack s!"/unit/boundary/x={x}/z={shift}"
                (runRshiftcHashModDirect shift #[intV x]) #[intV q, intV r] }
    ,
    { name := "/unit/pop-order/hash-immediate-preserves-lower-stack"
      run := do
        expectOkStack "/unit/pop-order/lower-null-preserved"
          (runRshiftcHashModDirect 1 #[.null, intV 7]) #[.null, intV 4, intV (-1)]
        expectOkStack "/unit/pop-order/lower-cell-preserved"
          (runRshiftcHashModDirect 2 #[.cell Cell.empty, intV (-13)])
          #[.cell Cell.empty, intV (-3), intV (-1)]
        expectOkStack "/unit/pop-order/lower-int-preserved"
          (runRshiftcHashModDirect 3 #[intV 42, intV 9])
          #[intV 42, intV 2, intV (-7)] }
    ,
    { name := "/unit/error-order/underflow-type-and-precedence"
      run := do
        expectErr "/unit/error/underflow/empty"
          (runRshiftcHashModDirect 1 #[]) .stkUnd
        expectErr "/unit/error/type/top-null"
          (runRshiftcHashModDirect 1 #[.null]) .typeChk
        expectErr "/unit/error/type/top-cell"
          (runRshiftcHashModDirect 1 #[.cell Cell.empty]) .typeChk
        expectErr "/unit/error-order/type-top-before-below-int"
          (runRshiftcHashModDirect 1 #[intV 7, .null]) .typeChk
        expectErr "/unit/error-order/type-top-before-below-shape"
          (runRshiftcHashModDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkRshiftcHashModInstr 1
        let instr256 := mkRshiftcHashModInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error err => throw (IO.userError s!"assemble failed: {err}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/rshiftc-hash-mod-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/rshiftc-hash-mod-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/opcode/assemble-hash-immediate-range-checked"
      run := do
        expectAssembleErr "/unit/assemble/shift0-range"
          (mkRshiftcHashModInstr 0) .rangeChk
        expectAssembleErr "/unit/assemble/shift257-range"
          (mkRshiftcHashModInstr 257) .rangeChk }
    ,
    { name := "/unit/dispatch/non-rshiftc-hash-mod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runRshiftcHashModDispatchFallback #[]) #[intV 8452] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/ceil/sign/pos-shift1" 1 #[.num 7],
    mkShiftInputCase "/ok/ceil/sign/neg-shift1" 1 #[.num (-7)],
    mkShiftInputCase "/ok/ceil/sign/pos-shift2" 2 #[.num 9],
    mkShiftInputCase "/ok/ceil/sign/neg-shift2" 2 #[.num (-9)],
    mkShiftInputCase "/ok/ceil/near-boundary/plus-one-shift1" 1 #[.num 1],
    mkShiftInputCase "/ok/ceil/near-boundary/minus-one-shift1" 1 #[.num (-1)],
    mkShiftInputCase "/ok/ceil/near-boundary/plus-two-shift1" 1 #[.num 2],
    mkShiftInputCase "/ok/ceil/near-boundary/minus-two-shift1" 1 #[.num (-2)],
    mkShiftInputCase "/ok/ceil/near-boundary/plus-seventeen-shift4" 4 #[.num 17],
    mkShiftInputCase "/ok/ceil/near-boundary/minus-seventeen-shift4" 4 #[.num (-17)],
    mkShiftInputCase "/ok/ceil/exact/divisible-pos-shift5" 5 #[.num 1024],
    mkShiftInputCase "/ok/ceil/exact/divisible-neg-shift5" 5 #[.num (-1024)],
    mkShiftInputCase "/ok/ceil/zero-shift128" 128 #[.num 0],
    mkShiftInputCase "/boundary/max-shift1" 1 #[.num maxInt257],
    mkShiftInputCase "/boundary/min-shift1" 1 #[.num minInt257],
    mkShiftInputCase "/boundary/max-shift255" 255 #[.num maxInt257],
    mkShiftInputCase "/boundary/min-shift255" 255 #[.num minInt257],
    mkShiftInputCase "/boundary/max-shift256" 256 #[.num maxInt257],
    mkShiftInputCase "/boundary/max-minus-one-shift256" 256 #[.num (maxInt257 - 1)],
    mkShiftInputCase "/boundary/min-shift256" 256 #[.num minInt257],
    mkShiftInputCase "/boundary/min-plus-one-shift256" 256 #[.num (minInt257 + 1)],
    mkShiftInputCase "/boundary/one-shift256" 256 #[.num 1],
    mkShiftInputCase "/boundary/minus-one-shift256" 256 #[.num (-1)],
    mkShiftInputCase "/boundary/pow255-shift256" 256 #[.num (pow2 255)],
    mkShiftInputCase "/boundary/neg-pow255-shift256" 256 #[.num (-(pow2 255))],
    mkShiftCase "/pop-order/lower-null-preserved" 1 #[.null, intV 7],
    mkShiftCase "/pop-order/lower-cell-preserved" 2 #[.cell Cell.empty, intV (-13)],
    mkShiftCase "/pop-order/lower-int-preserved" 3 #[intV 42, intV 9],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/type/top-null" 1 #[.null],
    mkShiftCase "/type/top-cell" 1 #[.cell Cell.empty],
    mkShiftCase "/error-order/type-top-before-below-int" 1 #[intV 7, .null],
    mkShiftCase "/error-order/type-top-before-below-shape" 1 #[.null, .cell Cell.empty],
    mkShiftInputCase "/intov/nan-x-via-program-shift1" 1 #[.nan],
    mkShiftInputCase "/intov/nan-x-via-program-shift256" 256 #[.nan],
    mkShiftInputCase "/error-order/pushint-overflow-high-before-op" 1 #[.num (maxInt257 + 1)],
    mkShiftInputCase "/error-order/pushint-overflow-low-before-op" 1 #[.num (minInt257 - 1)],
    mkShiftInputCase "/error-order/pushint-overflow-before-op-type-check"
      1 #[.num (pow2 257)] #[.null],
    mkShiftInputCase "/error-order/pushint-overflow-before-op-underflow"
      1 #[.num (-(pow2 257))],
    mkCase "/gas/exact-cost-succeeds/shift7" #[intV 7]
      #[.pushInt (.num rshiftcHashModSetGasExact), .tonEnvOp .setGasLimit, rshiftcHashModGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas/shift7" #[intV 7]
      #[.pushInt (.num rshiftcHashModSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftcHashModGasProbeInstr],
    mkCase "/gas/exact-cost-succeeds/shift256" #[intV 7]
      #[.pushInt (.num rshiftcHashModSetGasExact256), .tonEnvOp .setGasLimit, rshiftcHashModGasProbeInstr256],
    mkCase "/gas/exact-minus-one-out-of-gas/shift256" #[intV 7]
      #[.pushInt (.num rshiftcHashModSetGasExactMinusOne256), .tonEnvOp .setGasLimit, rshiftcHashModGasProbeInstr256]
  ]
  fuzz := #[
    { seed := 2026020898
      count := 768
      gen := genRshiftcHashModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFTC_HASH_MOD
