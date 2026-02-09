import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFTR_HASH_MOD

/-
RSHIFTR#MOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false false 3 0 false (some z)` specialization)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate SHR/MOD family `0xa93c..0xa93e`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, `0xa93c..0xa93e` decode to `.shrMod false false 3 ... (some z)`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`, underflow/type behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`mul=false`, `add=false`, `d=3`, `roundMode=0`, `quiet=false`, `zOpt=some z`):
- Lean specialization: 6 branch sites / 7 terminal outcomes
  (dispatch/fallback; depth gate; `x` pop type; numeric-vs-NaN split;
   quotient push fit-vs-`intOv`; remainder push fit-vs-`intOv`).
- C++ specialization: 6 branch sites / 7 aligned terminal outcomes
  (`check_underflow(1)`; const-shift decode route; `pop_int` type gate;
   `d=3` dual-result route; quotient/remainder push fit-vs-overflow).

Key risk areas covered:
- hash-immediate shift is encoded in opcode (`z` is never popped from stack);
- nearest rounding ties go toward `+∞` with signed remainder invariants;
- explicit underflow/type/error ordering and top-item pop order;
- NaN and out-of-range integer injection via `PUSHINT` prelude only;
- exact gas cliff with `PUSHINT n; SETGASLIMIT; RSHIFTR#MOD`.
-/

private def rshiftrHashModId : InstrId := { name := "RSHIFTR#MOD" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkRshiftrHashModInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod false false 3 0 false (some shift))

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := rshiftrHashModId
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
  mkCase name stack #[mkRshiftrHashModInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkRshiftrHashModInstr shift
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (programPrefix.push instr) gasLimits fuel

private def runRshiftrHashModDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkRshiftrHashModInstr shift) stack

private def runRshiftrHashModDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9371)) stack

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

private def rshiftrHashModGasProbeInstr : Instr :=
  mkRshiftrHashModInstr 7

private def rshiftrHashModSetGasExact : Int :=
  computeExactGasBudget rshiftrHashModGasProbeInstr

private def rshiftrHashModSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftrHashModGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tinyShiftPool : Array Nat :=
  #[1, 2, 3, 4, 5, 6, 7, 8]

private def smallSignedPool : Array Int :=
  #[-65, -33, -17, -13, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 13, 17, 33, 65]

private def tieOddPool : Array Int :=
  #[-17, -15, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11, 13, 15, 17]

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
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def classifyRshiftrHashMod (value : Int) (shift : Nat) : String :=
  let rem := modPow2Round value shift 0
  if rem = 0 then "ok-exact" else "ok-inexact"

private def genRshiftrHashModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (case0, rng2) :=
    if shape = 0 then
      let (value, rng2) := pickInt257Boundary rng1
      let (shift, rng3) := pickShiftBoundary rng2
      let kind := classifyRshiftrHashMod value shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-value-boundary-shift" shift #[intV value], rng3)
    else if shape = 1 then
      let (value, rng2) := pickSigned257ish rng1
      let (shift, rng3) := pickShiftInRange rng2
      let kind := classifyRshiftrHashMod value shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/random-value-random-shift" shift #[intV value], rng3)
    else if shape = 2 then
      let (value, rng2) := pickInt257Boundary rng1
      let (shift, rng3) := pickShiftInRange rng2
      let kind := classifyRshiftrHashMod value shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-value" shift #[intV value], rng3)
    else if shape = 3 then
      let (value, rng2) := pickSigned257ish rng1
      let (shift, rng3) := pickShiftBoundary rng2
      let kind := classifyRshiftrHashMod value shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift" shift #[intV value], rng3)
    else if shape = 4 then
      let (value, rng2) := pickIntFromPool tieOddPool rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/ok-inexact/tie-shift1" 1 #[intV value], rng2)
    else if shape = 5 then
      let (shift, rng2) := pickShiftInRange rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/ok-exact/zero-value" shift #[intV 0], rng2)
    else if shape = 6 then
      let (shift, rng2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty" shift #[], rng2)
    else if shape = 7 then
      let (shift, rng2) := pickShiftBoundary rng1
      let (badTop, rng3) := pickNonInt rng2
      (mkShiftCase s!"/fuzz/shape-{shape}/type/top-non-int" shift #[badTop], rng3)
    else if shape = 8 then
      let (value, rng2) := pickSigned257ish rng1
      let (shift, rng3) := pickShiftBoundary rng2
      let (badTop, rng4) := pickNonInt rng3
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/type-top-before-below-int"
        shift #[intV value, badTop], rng4)
    else if shape = 9 then
      let (value, rng2) := pickIntFromPool smallSignedPool rng1
      let (shift, rng3) := pickShiftInRange rng2
      let (below, rng4) := pickNonInt rng3
      let kind := classifyRshiftrHashMod value shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/pop-order/below-preserved"
        shift #[below, intV value], rng4)
    else if shape = 10 then
      let (shift, rng2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program"
        shift #[.nan], rng2)
    else if shape = 11 then
      let (shift, rng2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-high-before-op"
        shift #[.num (maxInt257 + 1)], rng2)
    else if shape = 12 then
      let (shift, rng2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-low-before-op"
        shift #[.num (minInt257 - 1)], rng2)
    else if shape = 13 then
      let (pickMax, rng2) := randBool rng1
      let value := if pickMax then maxInt257 else minInt257
      let kind := classifyRshiftrHashMod value 1
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift1-extreme" 1 #[intV value], rng2)
    else if shape = 14 then
      let (pickMax, rng2) := randBool rng1
      let value := if pickMax then maxInt257 else minInt257
      let kind := classifyRshiftrHashMod value 256
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift256-extreme" 256 #[intV value], rng2)
    else if shape = 15 then
      let (quotientSeed, rng2) := pickIntFromPool smallSignedPool rng1
      let (shift, rng3) := pickNatFromPool tinyShiftPool rng2
      let value := quotientSeed * intPow2 shift
      (mkShiftCase s!"/fuzz/shape-{shape}/ok-exact/constructed-divisible"
        shift #[intV value], rng3)
    else if shape = 16 then
      let (value, rng2) := pickIntFromPool smallSignedPool rng1
      let (shift, rng3) := pickNatFromPool tinyShiftPool rng2
      let kind := classifyRshiftrHashMod value shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/small-signed" shift #[intV value], rng3)
    else if shape = 17 then
      let (shift, rng2) := pickShiftBoundary rng1
      let (below, rng3) := pickNonInt rng2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-with-below-via-program"
        shift #[.nan] #[below], rng3)
    else if shape = 18 then
      let (value, rng2) := pickSigned257ish rng1
      let (shift, rng3) := pickShiftBoundary rng2
      let (below, rng4) := pickNonInt rng3
      let kind := classifyRshiftrHashMod value shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/pop-order/below-preserved-boundary-shift"
        shift #[below, intV value], rng4)
    else
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/fallback" 1 #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := rshiftrHashModId
  unit := #[
    { name := "/unit/direct/nearest-rounding-and-remainder-invariants"
      run := do
        let checks : Array (Int × Nat × Int × Int) :=
          #[
            (7, 1, 4, -1),
            (-7, 1, -3, -1),
            (5, 1, 3, -1),
            (-5, 1, -2, -1),
            (3, 1, 2, -1),
            (-3, 1, -1, -1),
            (1, 1, 1, -1),
            (-1, 1, 0, -1),
            (7, 2, 2, -1),
            (-7, 2, -2, 1),
            (9, 3, 1, 1),
            (-9, 3, -1, -1),
            (40, 3, 5, 0),
            (-40, 3, -5, 0),
            (maxInt257, 1, pow2 255, -1),
            (minInt257, 1, -(pow2 255), 0),
            (maxInt257, 256, 1, -1),
            (minInt257, 256, -1, 0),
            (pow2 255, 256, 1, -(pow2 255)),
            (-(pow2 255), 256, 0, -(pow2 255))
          ]
        for entry in checks do
          match entry with
          | (value, shift, expectedQuot, expectedRem) =>
              expectOkStack s!"/unit/direct/value={value}/z={shift}"
                (runRshiftrHashModDirect shift #[intV value]) #[intV expectedQuot, intV expectedRem] }
    ,
    { name := "/unit/direct/pop-order-and-below-preservation"
      run := do
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runRshiftrHashModDirect 1 #[.null, intV 7]) #[.null, intV 4, intV (-1)]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runRshiftrHashModDirect 2 #[.cell Cell.empty, intV (-13)])
          #[.cell Cell.empty, intV (-3), intV (-1)]
        expectOkStack "/unit/pop-order/below-int-preserved"
          (runRshiftrHashModDirect 3 #[intV 42, intV 9])
          #[intV 42, intV 1, intV 1] }
    ,
    { name := "/unit/error/underflow-type-and-order"
      run := do
        expectErr "/unit/error/underflow/empty"
          (runRshiftrHashModDirect 1 #[]) .stkUnd
        expectErr "/unit/error/type/top-null"
          (runRshiftrHashModDirect 1 #[.null]) .typeChk
        expectErr "/unit/error/type/top-cell"
          (runRshiftrHashModDirect 1 #[.cell Cell.empty]) .typeChk
        expectErr "/unit/error-order/type-top-before-below-int"
          (runRshiftrHashModDirect 1 #[intV 7, .null]) .typeChk
        expectErr "/unit/error-order/type-on-top-before-below-shape"
          (runRshiftrHashModDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkRshiftrHashModInstr 1
        let instr256 := mkRshiftrHashModInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error err => throw (IO.userError s!"assemble failed: {err}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/rshiftr-hash-mod-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/rshiftr-hash-mod-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/opcode/encode-invalid-immediate-range"
      run := do
        let invalidLow := mkRshiftrHashModInstr 0
        let invalidHigh := mkRshiftrHashModInstr 257
        match assembleCp0 [invalidLow] with
        | .ok _ =>
            throw (IO.userError "/unit/encode/range/shift0: expected rangeChk, got ok")
        | .error err =>
            if err = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"/unit/encode/range/shift0: expected rangeChk, got {err}")
        match assembleCp0 [invalidHigh] with
        | .ok _ =>
            throw (IO.userError "/unit/encode/range/shift257: expected rangeChk, got ok")
        | .error err =>
            if err = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"/unit/encode/range/shift257: expected rangeChk, got {err}") }
    ,
    { name := "/unit/dispatch/non-rshiftr-hash-mod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runRshiftrHashModDispatchFallback #[]) #[intV 9371] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/nearest/tie/plus-half-shift1" 1 #[.num 1],
    mkShiftInputCase "/ok/nearest/tie/minus-half-shift1" 1 #[.num (-1)],
    mkShiftInputCase "/ok/nearest/tie/plus-three-halves-shift1" 1 #[.num 3],
    mkShiftInputCase "/ok/nearest/tie/minus-three-halves-shift1" 1 #[.num (-3)],
    mkShiftInputCase "/ok/nearest/inexact/pos-shift2" 2 #[.num 7],
    mkShiftInputCase "/ok/nearest/inexact/neg-shift2" 2 #[.num (-7)],
    mkShiftInputCase "/ok/nearest/exact/pos-shift3" 3 #[.num 40],
    mkShiftInputCase "/ok/nearest/exact/neg-shift3" 3 #[.num (-40)],
    mkShiftInputCase "/ok/nearest/inexact/pos-shift3" 3 #[.num 9],
    mkShiftInputCase "/ok/nearest/inexact/neg-shift3" 3 #[.num (-9)],
    mkShiftInputCase "/ok/boundary/max-shift1" 1 #[.num maxInt257],
    mkShiftInputCase "/ok/boundary/min-shift1" 1 #[.num minInt257],
    mkShiftInputCase "/ok/boundary/max-shift256" 256 #[.num maxInt257],
    mkShiftInputCase "/ok/boundary/min-shift256" 256 #[.num minInt257],
    mkShiftInputCase "/ok/boundary/max-minus-one-shift256" 256 #[.num (maxInt257 - 1)],
    mkShiftInputCase "/ok/boundary/min-plus-one-shift256" 256 #[.num (minInt257 + 1)],
    mkShiftInputCase "/ok/boundary/pow255-shift256" 256 #[.num (pow2 255)],
    mkShiftInputCase "/ok/boundary/neg-pow255-shift256" 256 #[.num (-(pow2 255))],
    mkShiftCase "/ok/pop-order/below-null-preserved" 1 #[.null, intV 7],
    mkShiftCase "/ok/pop-order/below-cell-preserved" 2 #[.cell Cell.empty, intV (-13)],
    mkShiftCase "/ok/pop-order/below-int-preserved" 3 #[intV 42, intV 9],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/type/top-null" 1 #[.null],
    mkShiftCase "/type/top-cell" 1 #[.cell Cell.empty],
    mkShiftCase "/error-order/type-top-before-below-int" 1 #[intV 7, .null],
    mkShiftCase "/error-order/type-on-top-before-below-shape" 1 #[.null, .cell Cell.empty],
    mkShiftInputCase "/intov/nan-x-via-program" 1 #[.nan],
    mkShiftInputCase "/intov/nan-x-with-below-via-program" 2 #[.nan] #[.null],
    mkShiftInputCase "/error-order/pushint-overflow-x-high-before-op"
      1 #[.num (maxInt257 + 1)],
    mkShiftInputCase "/error-order/pushint-overflow-x-low-before-op"
      1 #[.num (minInt257 - 1)],
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op-shift256"
      256 #[.num (pow2 257)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num rshiftrHashModSetGasExact), .tonEnvOp .setGasLimit, rshiftrHashModGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num rshiftrHashModSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftrHashModGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020894
      count := 700
      gen := genRshiftrHashModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFTR_HASH_MOD
