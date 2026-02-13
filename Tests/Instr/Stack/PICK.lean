import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Stack.PICK

/-!
INSTRUCTION: PICK

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch gate.
   - `execInstrStackPick` executes the `PICK` path only for `.pick`; otherwise it delegates
     to `next`.
   - This is explicitly tested via unit fallback behavior.

2. [B2] Runtime normal path with `x = 0`.
   - `popNatUpTo` succeeds, `x` remains in bounds, and `fetch 0` pushes a copy of the current
     top element.
   - Equivalent to a no-op on stack-depth for the selector but with an extra top duplication.

3. [B3] Runtime normal path with `0 < x < st.stack.size`.
   - Valid in-range index selects the `(x+1)`-th element from the bottom (`st.stack.size - 1 - x`).
   - Result is stack append with that selected value copied to top.

4. [B4] `popNatUpTo` precondition failures (before stack-depth check):
   - Empty stack at `popInt`: throws `.stkUnd`.
   - Non-integer top of stack: throws `.typeChk`.
   - Integer conversion/validation failures (NaN, negative, over max): throws `.rangeChk`.

5. [B5] Post-pop depth guard failure.
   - After valid `x` is parsed, if `x ≥ st.stack.size` the handler throws `.stkUnd`.

6. [B6] Assembler encoding and immediate-parameter branching.
   - No immediate operands for `.pick`; assembler emits exact 8-bit opcode `0x60`.
   - There is no `rangeChk`/`range`-style rejection in assembly (assembly-rejection branch is absent
     in Lean for PICK).

7. [B7] Decoder behavior.
   - Single-byte opcode `0x60` decodes to `.pick` with 8 bits consumed.
   - Neighboring opcode `0x61` decodes to `.roll` (distinguishable boundary in same family class).
   - Incomplete/truncated prefixes and non-opcodes must fail with decode error.

8. [B8] Gas accounting.
   - Spec/implementation indicate fixed gas for PICK (`base=18`, no variable penalty on `x`).
   - Exact-base gas should succeed.
   - Exact-minus-one budget should fail with out-of-gas.

9. [B9] Spec aliasing metadata.
- TVM spec JSON includes `PUSHX` aliasing to `actual_name = PICK`; this does not create a distinct
  Lean/C++ opcode path in this codebase, so there is no executable alias decode/branch to test here.

TOTAL BRANCHES: 9

Each oracle test below is tagged [Bn] to indicate branch coverage.
Aliasing branch [B9] is external metadata-only and is satisfied by the branch analysis statement above.
-/

private def pickId : InstrId := { name := "PICK" }
private def pickInstr : Instr := .pick

private def maxPickOffset : Nat := (1 <<< 30) - 1
private def tooLargePickOffset : Int := (1 <<< 30)

private def pickOpcode : Cell := Cell.mkOrdinary (natToBits 0x60 8) #[]
private def blkPushFamilyPrefix : Cell := Cell.mkOrdinary (natToBits 0x5f 8) #[]
private def truncatedPick7 : Cell := Cell.mkOrdinary (natToBits 0x60 7) #[]
private def unknown8 : Cell := Cell.mkOrdinary (natToBits 0xFF 8) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[pickInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pickId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value := #[])
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pickId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkPickStack (below : Nat) (top : Int) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:below] do
      out := out.push (intV (Int.ofNat (i + 1)))
    return out.push (intV top)

private def runPickDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPick pickInstr stack

private def runPickDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPick .add (VM.push (intV 909)) stack

private def expectDecodeErr (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e != .invOpcode then
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, used, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {instr} after consuming {used} bits")

private def pickGasExact : Int := computeExactGasBudget pickInstr
private def pickGasExactMinusOne : Int := computeExactGasBudgetMinusOne pickInstr
private def pickGasExactLimits : OracleGasLimits := oracleGasLimitsExact pickGasExact
private def pickGasExactMinusOneLimits : OracleGasLimits :=
  oracleGasLimitsExactMinusOne pickGasExact

private def genPickFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (baseCase, rng2) :=
    if shape = 0 then
      let (size, rng2) := randNat rng1 1 24
      (mkCase s!"fuzz/ok/x0-size-{size}" (mkPickStack size 0), rng2)
    else if shape = 1 then
      let (x, rng2) := randNat rng1 1 12
      let (extra, rng3) := randNat rng2 0 6
      (mkCase s!"fuzz/ok/x{x}" (mkPickStack (x + extra) (Int.ofNat x)), rng3)
    else if shape = 2 then
      let (choice, rng2) := randNat rng1 0 1
      let x : Nat := if choice = 0 then 255 else 256
      let (extra, rng3) := randNat rng2 0 8
      (mkCase s!"fuzz/ok/x{x}" (mkPickStack (x + extra) (Int.ofNat x)), rng3)
    else if shape = 3 then
      let (x, rng2) := randNat rng1 16 63
      let (extra, rng3) := randNat rng2 0 12
      (mkCase s!"fuzz/ok/x{x}-deep" (mkPickStack (x + extra) (Int.ofNat x)), rng3)
    else if shape = 4 then
      (mkCase "fuzz/ok/mixed-below-types"
        #[intV 10, .null, .cell Cell.empty, .tuple #[], .builder Builder.empty, intV 3], rng1)
    else if shape = 5 then
      (mkCase "fuzz/err/empty-pre-pop" #[], rng1)
    else if shape = 6 then
      (mkCase "fuzz/err/type-top-null" #[.null, intV 7], rng1)
    else if shape = 7 then
      (mkCase "fuzz/err/type-top-cell" #[.cell Cell.empty, intV 7], rng1)
    else if shape = 8 then
      (mkCase "fuzz/err/range-top-negative" #[intV (-1)], rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/range-top-too-large" #[intV tooLargePickOffset, intV 7], rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/underflow-stack-size-eq" (mkPickStack 0 1), rng1)
    else if shape = 11 then
      let (size, rng2) := randNat rng1 0 8
      let (extra, rng3) := randNat rng2 0 12
      let x : Nat := size + 1 + extra
      (mkCase s!"fuzz/err/underflow-stack-size-large-x{x}" (mkPickStack size (Int.ofNat x)), rng3)
    else if shape = 12 then
      (mkCodeCase "fuzz/decode-raw-pick" (mkPickStack 2 0) pickOpcode, rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/range-top-nan"
        #[]
        #[.pushInt (.nan), pickInstr] , rng1)
    else if shape = 14 then
      (mkCase "fuzz/gas/exact"
        #[intV 7, intV 0]
        #[.pushInt (.num pickGasExact), .tonEnvOp .setGasLimit, pickInstr]
        pickGasExactLimits, rng1)
    else if shape = 15 then
      (mkCase "fuzz/gas/exact-minus-one"
        #[intV 7, intV 0]
        #[.pushInt (.num pickGasExactMinusOne), .tonEnvOp .setGasLimit, pickInstr]
        pickGasExactMinusOneLimits, rng1)
    else if shape = 16 then
      let (size, rng2) := randNat rng1 1 6
      (mkCase "fuzz/ok/x3-large-stack" (mkPickStack (3 + size) 3), rng2)
    else
      (mkCodeCase "fuzz/decode/invalid" #[] unknown8, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr pickId

def suite : InstrSuite where
  id := pickId
  unit := #[
    { name := "unit/dispatch/fallback-to-next" -- [B1]
      run := do
        let _ ← expectOkStack "dispatch-fallback"
          (runPickDispatchFallback #[intV 7, intV 11]) #[intV 7, intV 11, intV 909] },
    { name := "unit/direct/success-x0-and-x2" -- [B2][B3]
      run := do
        expectOkStack "x0" (runPickDirect #[intV 42]) #[intV 42, intV 42]
        expectOkStack "x2" (runPickDirect #[intV 1, intV 2, intV 3, intV 2])
          #[intV 1, intV 2, intV 3, intV 2, intV 2] },
    { name := "unit/direct/error-cases" -- [B4][B5]
      run := do
        expectErr "empty-stk" (runPickDirect #[]) .stkUnd
        expectErr "type-null" (runPickDirect #[.null]) .typeChk
        expectErr "range-neg" (runPickDirect #[intV (-1)]) .rangeChk
        expectErr "range-too-big" (runPickDirect #[intV tooLargePickOffset]) .rangeChk
        expectErr "underflow-post-pop" (runPickDirect #[intV 2, intV 9]) .stkUnd },
    { name := "unit/opcode/assemble-encode"
      run := do
        let code ←
          match assembleCp0 [pickInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble pick failed: {e}")
        if code.bits = natToBits 0x60 8 then
          pure ()
        else
          throw (IO.userError s!"assemble pick expected 0x60, got {code.bits}") },
    { name := "unit/opcode/decode-boundaries"
      run := do
        let s0 := Slice.ofCell (Cell.mkOrdinary (natToBits 0x60 8 ++ natToBits 0x61 8) #[])
        let s1 ← expectDecodeStep "decode/pick" s0 pickInstr 8
        let s2 ← expectDecodeStep "decode/roll-neighbor" s1 .roll 8
        if s2.bitsRemaining + s2.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError "decode boundary should have consumed all bits")
        expectDecodeErr "decode/truncated-7" truncatedPick7
        expectDecodeErr "decode/truncated-5f" blkPushFamilyPrefix
        expectDecodeErr "decode-unknown" unknown8
        pure () 
    }
  ]
  oracle := #[
    mkCase "ok/x0-size-1" (mkPickStack 0 0), -- [B2]
    mkCase "ok/x0-size-1-mixed" #[intV 11, intV 22, .cell Cell.empty, intV 0], -- [B2]
    mkCase "ok/x0-size-8" (mkPickStack 8 0), -- [B2]
    mkCase "ok/x1" (mkPickStack 1 1), -- [B3]
    mkCase "ok/x2" (mkPickStack 2 2), -- [B3]
    mkCase "ok/x3" (mkPickStack 3 3), -- [B3]
    mkCase "ok/x4" (mkPickStack 4 4), -- [B3]
    mkCase "ok/x5" (mkPickStack 5 5), -- [B3]
    mkCase "ok/x7" (mkPickStack 7 7), -- [B3]
    mkCase "ok/x16" (mkPickStack 16 16), -- [B3]
    mkCase "ok/x63" (mkPickStack 63 63), -- [B3]
    mkCase "ok/x64" (mkPickStack 64 64), -- [B3]
    mkCase "ok/x128" (mkPickStack 128 128), -- [B3]
    mkCase "ok/x255" (mkPickStack 255 255), -- [B3]
    mkCase "ok/x256" (mkPickStack 256 256), -- [B3]
    mkCase "ok/xdeep/mixed-below" #[intV 10, .null, .cell Cell.empty, .tuple #[], .builder Builder.empty, intV 3], -- [B3]
    mkCase "err/empty" #[], -- [B4]
    mkCase "err/type-null" #[.null, intV 7], -- [B4]
    mkCase "err/type-cell" #[.cell Cell.empty, intV 7], -- [B4]
    mkCase "err/type-builder" #[.builder Builder.empty, intV 7], -- [B4]
    mkCase "err/type-tuple" #[.tuple #[], intV 7], -- [B4]
    mkCase "err/type-cont" #[.cont (.quit 0), intV 7], -- [B4]
    mkCase "err/range-top-negative" #[intV (-1)], -- [B5]
    mkCase "err/range-top-negative-small" #[intV (-257)], -- [B5]
    mkCase "err/range-top-over-max" #[intV tooLargePickOffset], -- [B5]
    mkCase "err/range-top-over-max-3" #[intV (tooLargePickOffset + 3)], -- [B5]
    mkCase "err/range-top-nan" #[]
      #[.pushInt (.nan), pickInstr], -- [B5]
    mkCase "err/underflow-size-eq" (mkPickStack 0 1), -- [B6]
    mkCase "err/underflow-size-greater" (mkPickStack 1 3), -- [B6]
    mkCase "err/underflow-size-mixed" (mkPickStack 2 9), -- [B6]
    mkCodeCase "decode/ok/raw-pick" (mkPickStack 1 0) pickOpcode, -- [B7]
    mkCodeCase "decode/ok/raw-pick-with-trailing" (mkPickStack 1 0) (Cell.mkOrdinary (natToBits 0x60 8 ++ natToBits 0x00 8) #[]), -- [B7]
    mkCase "gas/exact" (mkPickStack 1 0)
      #[.pushInt (.num pickGasExact), .tonEnvOp .setGasLimit, pickInstr]
      pickGasExactLimits, -- [B8]
    mkCase "gas/exact-minus-one" (mkPickStack 1 0)
      #[.pushInt (.num pickGasExactMinusOne), .tonEnvOp .setGasLimit, pickInstr]
      pickGasExactMinusOneLimits -- [B8]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genPickFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.PICK
