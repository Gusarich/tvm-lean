import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.PUSHPOW2DEC

/-
PUSHPOW2DEC branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Stack/PushPow2Dec.lean`
    (`execInstrStackPushPow2Dec`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.pushIntQuiet`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` / `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0x84` + 8-bit immediate decode/encode for `PUSHPOW2DEC`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_push_pow2dec`, opcode wiring in `register_int_const_ops`)

Branch counts used for this suite:
- Lean: 3 branch points / 5 terminal outcomes
  (opcode dispatch; `pushIntQuiet` signed-257 fit gate; fallback-next path).
- C++: 2 branch points / 3 aligned outcomes
  (fixed `0x84` decode arm + immediate `args+1`; unconditional push path),
  plus VM-level gas precharge failure outside opcode body.

Mapped outcomes covered:
- success for exponents `1..256` with pushed value `2^exp - 1`;
- below-stack preservation (int/non-int/NaN below top);
- exact gas success and exact-minus-one out-of-gas cliff;
- direct-handler out-of-spec overflow (`exp = 257`) yielding `intOv`.

Prelude injection rules used in this suite:
- slash case naming is used consistently (`/group/subgroup/...`);
- oracle/fuzz cases never place non-serializable integer probes directly in `initStack`;
  they are injected via program prelude using `oracleIntInputsToStackOrProgram`;
- prelude failures (e.g. out-of-range `PUSHINT`) are asserted as pre-op outcomes.
-/

private def pushpow2decId : InstrId := { name := "PUSHPOW2DEC" }

private def pushpow2decInstr (exp : Nat) : Instr :=
  .pushPow2Dec exp

private def pow2DecValue (exp : Nat) : Int :=
  intPow2 exp - 1

private def mkCaseWithProgram
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pushpow2decId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCase
    (name : String)
    (exp : Nat)
    (stack : Array Value := #[])
    (programPrefix : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCaseWithProgram name stack (programPrefix.push (pushpow2decInstr exp)) gasLimits fuel

private def mkCaseFromBelowIntVals
    (name : String)
    (exp : Nat)
    (below : Array IntVal)
    (programPrefix : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, prelude) := oracleIntInputsToStackOrProgram below
  mkCaseWithProgram
    name
    stack
    (prelude ++ programPrefix ++ #[pushpow2decInstr exp])
    gasLimits
    fuel

private def mkGasCase
    (name : String)
    (exp : Nat)
    (stack : Array Value)
    (budget : Int) : OracleCase :=
  mkCase
    name
    exp
    stack
    #[.pushInt (.num budget), .tonEnvOp .setGasLimit]

private def mkGasCaseFromBelowIntVals
    (name : String)
    (exp : Nat)
    (below : Array IntVal)
    (budget : Int) : OracleCase :=
  mkCaseFromBelowIntVals
    name
    exp
    below
    #[.pushInt (.num budget), .tonEnvOp .setGasLimit]

private def runPushpow2decDirect (exp : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPushPow2Dec (pushpow2decInstr exp) stack

private def runPushpow2decDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPushPow2Dec .add (VM.push (intV 991)) stack

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

private def pushpow2decGasProbeExp : Nat := 17

private def pushpow2decSetGasExact : Int :=
  computeExactGasBudget (pushpow2decInstr pushpow2decGasProbeExp)

private def pushpow2decSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (pushpow2decInstr pushpow2decGasProbeExp)

private def expBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 31, 63, 127, 255, 256]

private def nonSerializableBelowPool : Array IntVal :=
  #[.nan, .num (maxInt257 + 1), .num (minInt257 - 1)]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickExpMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    pickFromPool expBoundaryPool rng1
  else
    randNat rng1 1 256

private def genPushpow2decFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (exp, rng2) := pickExpMixed rng1
  let (case0, rng3) :=
    if shape = 0 then
      (mkCase s!"/fuzz/shape-{shape}/ok/empty/exp-{exp}" exp, rng2)
    else if shape = 1 then
      let (below, r3) := pickInt257Boundary rng2
      (mkCase s!"/fuzz/shape-{shape}/ok/below-int257-boundary/exp-{exp}" exp #[intV below], r3)
    else if shape = 2 then
      let (below, r3) := pickSigned257ish rng2
      (mkCase s!"/fuzz/shape-{shape}/ok/below-int257-random/exp-{exp}" exp #[intV below], r3)
    else if shape = 3 then
      let (a, r3) := pickSigned257ish rng2
      let (b, r4) := pickSigned257ish r3
      (mkCase s!"/fuzz/shape-{shape}/ok/below-two-ints/exp-{exp}" exp #[intV a, intV b], r4)
    else if shape = 4 then
      let (pickNull, r3) := randBool rng2
      let below : Value := if pickNull then .null else .cell Cell.empty
      let kind := if pickNull then "null" else "cell"
      (mkCase s!"/fuzz/shape-{shape}/ok/below-{kind}/exp-{exp}" exp #[below], r3)
    else if shape = 5 then
      (mkCaseFromBelowIntVals s!"/fuzz/shape-{shape}/prelude/below-nan/exp-{exp}" exp #[.nan], rng2)
    else if shape = 6 then
      let (below, r3) := pickSigned257ish rng2
      (mkCaseFromBelowIntVals
        s!"/fuzz/shape-{shape}/prelude/below-int-and-nan/exp-{exp}"
        exp
        #[.num below, .nan], r3)
    else if shape = 7 then
      (mkCaseFromBelowIntVals
        s!"/fuzz/shape-{shape}/prelude/pushint-overflow-high-before-op/exp-{exp}"
        exp
        #[.num (maxInt257 + 1)], rng2)
    else if shape = 8 then
      (mkCaseFromBelowIntVals
        s!"/fuzz/shape-{shape}/prelude/pushint-overflow-low-before-op/exp-{exp}"
        exp
        #[.num (minInt257 - 1)], rng2)
    else if shape = 9 then
      (mkGasCase
        s!"/fuzz/shape-{shape}/gas/exact/exp-{exp}"
        exp
        #[]
        pushpow2decSetGasExact, rng2)
    else if shape = 10 then
      (mkGasCase
        s!"/fuzz/shape-{shape}/gas/exact-minus-one/exp-{exp}"
        exp
        #[]
        pushpow2decSetGasExactMinusOne, rng2)
    else if shape = 11 then
      let (below, r3) := pickInt257Boundary rng2
      (mkGasCase
        s!"/fuzz/shape-{shape}/gas/exact/below-int/exp-{exp}"
        exp
        #[intV below]
        pushpow2decSetGasExact, r3)
    else
      let (idx, r3) := randNat rng2 0 (nonSerializableBelowPool.size - 1)
      let below :=
        match nonSerializableBelowPool.get? idx with
        | some v => v
        | none => .nan
      (mkCaseFromBelowIntVals s!"/fuzz/shape-{shape}/prelude/mixed-nonserializable/exp-{exp}" exp #[below], r3)
  let (tag, rng4) := randNat rng3 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng4)

def suite : InstrSuite where
  id := pushpow2decId
  unit := #[
    { name := "/unit/direct/success-boundaries-and-stack-order"
      run := do
        let exps : Array Nat := #[1, 2, 8, 31, 127, 255, 256]
        for exp in exps do
          expectOkStack
            s!"/unit/direct/exp-{exp}"
            (runPushpow2decDirect exp #[])
            #[intV (pow2DecValue exp)]
        expectOkStack
          "/unit/direct/below-int-preserved"
          (runPushpow2decDirect 8 #[intV 99])
          #[intV 99, intV (pow2DecValue 8)]
        expectOkStack
          "/unit/direct/below-null-preserved"
          (runPushpow2decDirect 8 #[.null])
          #[.null, intV (pow2DecValue 8)]
        expectOkStack
          "/unit/direct/below-nan-preserved"
          (runPushpow2decDirect 8 #[.int .nan])
          #[.int .nan, intV (pow2DecValue 8)] }
    ,
    { name := "/unit/direct/out-of-spec-exp257-intov"
      run := do
        expectErr "/unit/direct/exp-257" (runPushpow2decDirect 257 #[]) .intOv }
    ,
    { name := "/unit/decode/fixed-sequence"
      run := do
        let program : Array Instr :=
          #[pushpow2decInstr 1, pushpow2decInstr 255, pushpow2decInstr 256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/exp-1" s0 (pushpow2decInstr 1) 16
        let s2 ← expectDecodeStep "/unit/decode/exp-255" s1 (pushpow2decInstr 255) 16
        let s3 ← expectDecodeStep "/unit/decode/exp-256" s2 (pushpow2decInstr 256) 16
        let s4 ← expectDecodeStep "/unit/decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/assembler/range-check"
      run := do
        expectAssembleErr "/unit/assembler/exp-0" [pushpow2decInstr 0] .rangeChk
        expectAssembleErr "/unit/assembler/exp-257" [pushpow2decInstr 257] .rangeChk }
    ,
    { name := "/unit/dispatch/non-pushpow2dec-falls-through"
      run := do
        expectOkStack
          "/unit/dispatch/fallback"
          (runPushpow2decDispatchFallback #[])
          #[intV 991] }
  ]
  oracle := #[
    mkCase "/ok/exp-1" 1,
    mkCase "/ok/exp-2" 2,
    mkCase "/ok/exp-8" 8,
    mkCase "/ok/exp-31" 31,
    mkCase "/ok/exp-127" 127,
    mkCase "/ok/exp-255" 255,
    mkCase "/ok/exp-256-max-int257" 256,
    mkCase "/ok/below-int-preserved" 8 #[intV 77],
    mkCase "/ok/below-null-preserved" 8 #[.null],
    mkCase "/ok/below-cell-preserved" 8 #[.cell Cell.empty],
    mkCaseFromBelowIntVals "/prelude/below-nan-via-pushint" 8 #[.nan],
    mkCaseFromBelowIntVals
      "/prelude/pushint-overflow-high-before-op"
      8
      #[.num (maxInt257 + 1)],
    mkCaseFromBelowIntVals
      "/prelude/pushint-overflow-low-before-op"
      8
      #[.num (minInt257 - 1)],
    mkGasCase
      "/gas/exact-cost-succeeds"
      pushpow2decGasProbeExp
      #[]
      pushpow2decSetGasExact,
    mkGasCase
      "/gas/exact-minus-one-out-of-gas"
      pushpow2decGasProbeExp
      #[]
      pushpow2decSetGasExactMinusOne,
    mkGasCaseFromBelowIntVals
      "/gas/exact/below-nan-prelude"
      pushpow2decGasProbeExp
      #[.nan]
      pushpow2decSetGasExact
  ]
  fuzz := #[
    { seed := 2026020817
      count := 700
      gen := genPushpow2decFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.PUSHPOW2DEC
