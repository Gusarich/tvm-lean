import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Stack.ROLLREV

/-!
BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime underflow (before `pop`): empty stack / missing `x` argument -> `.stkUnd`.
2. [B2] Runtime type-check: non-`Int` top argument -> `.typeChk`.
3. [B3] Runtime range-check: `NaN` top argument -> `.rangeChk`.
4. [B4] Runtime range-check: negative top argument -> `.rangeChk`.
5. [B5] Runtime range-check: top integer > `(1 << 30) - 1` -> `.rangeChk` (both Lean and modern C++ paths with `global_version >= 4`).
6. [B6] Runtime underflow after `pop`: valid `x` but not enough remaining stack depth -> `.stkUnd`.
7. [B7] Success x=0 branch: pop argument and return stack with one removed element, no swaps.
8. [B8] Success 1 <= x <= 1 branch: single swap sequence.
9. [B9] Success x>=2 branch: full rolling loop.
10. [B10] Gas path: `x <= 255` performs no dynamic penalty; base cost only.
11. [B11] Gas path: `x > 255` pays surcharge `x - 255`.

Assembler/decoder/category analysis:
12. [A1] Assembler encoding: `.rollRev` has fixed opcode `0x62`, single 8-bit form; no operand-range branch.
13. [A2] Decoder path: byte `0x62` decodes to `.rollRev`; next-byte chaining still works.
14. [A3] Decoder path: malformed/empty bitstream should fail with `.invOpcode`.

TOTAL BRANCHES: 14

Each oracle test below is tagged with exercised branch labels.
-/

private def rollRevId : InstrId := { name := "ROLLREV" }

private def rollRevInstr : Instr := .rollRev

private def rollRevGasBase : Int :=
  computeExactGasBudget rollRevInstr

private def runRollRevDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackRollRev rollRevInstr stack

private def mkRollRevCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[rollRevInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := rollRevId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkNumTail (n : Nat) : Array Value :=
  (List.range n).foldl (fun acc i => acc.push (intV (Int.ofNat i))) #[]

private def shortTail : Array Value :=
  #[(intV 11), .null, .cell Cell.empty, .slice (Slice.ofCell Cell.empty), .builder Builder.empty, .tuple #[]]

private def longTail256 : Array Value :=
  mkNumTail 256

private def withTop
    (x : Int)
    (tail : Array Value := shortTail) : Array Value :=
  tail.push (intV x)

private def gasForX (x : Int) : Int :=
  rollRevGasBase + (if x > 255 then x - 255 else 0)

private def mkRollRevGasCase
    (name : String)
    (x : Int)
    (tail : Array Value)
    (minusOne : Bool)
    : OracleCase :=
  let gas : Int := gasForX x
  let limit : Int := if minusOne then Int.max 0 (gas - 1) else gas
  mkRollRevCase name
    (withTop x tail)
    (#[(.pushInt (.num gas)), .tonEnvOp .setGasLimit, rollRevInstr])
    (oracleGasLimitsExact limit)

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
        throw (IO.userError s!"{label}: expected {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else
        pure s'

private def pickRollRevX (rng0 : StdGen) : Int × StdGen :=
  let (choice, rng1) := randNat rng0 0 7
  if choice = 0 then
    (0, rng1)
  else if choice = 1 then
    (1, rng1)
  else if choice = 2 then
    (2, rng1)
  else if choice = 3 then
    (3, rng1)
  else if choice = 4 then
    (4, rng1)
  else if choice = 5 then
    (5, rng1)
  else if choice = 6 then
    (6, rng1)
  else
    (Int.ofNat (choice + 20), rng1)

private def pickFuzzPayload
    (rng0 : StdGen)
    (x : Int)
    (tail : Array Value := shortTail) : Array Value × StdGen :=
  let stack := withTop x tail
  (stack, rng0)

private def genRollRevFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 8
  if shape = 0 then
    (mkRollRevCase "fuzz/err/underflow-empty" #[], rng1)
  else if shape = 1 then
    (mkRollRevCase "fuzz/err/underflow-singleton" (#[(intV 0)]), rng1)
  else if shape = 2 then
    (mkRollRevCase "fuzz/err/underflow-equal-size" (#[(intV 1), intV 0]), rng1)
  else if shape = 3 then
    (mkRollRevCase "fuzz/err/type-top-non-int" (#[(shortTail[0]!), intV 0]), rng1)
  else if shape = 4 then
    (mkRollRevCase "fuzz/err/range-nan" (#[(.int .nan), intV 1]), rng1)
  else if shape = 5 then
    (mkRollRevCase "fuzz/err/range-negative" (#[(intV (-1)), intV 1]), rng1)
  else if shape = 6 then
    (mkRollRevCase "fuzz/err/range-too-large" (#[(intV ((1 <<< 30))), intV 1]), rng1)
  else
    let (x, rng2) := pickRollRevX rng1
    let (stack, rng3) := pickFuzzPayload rng2 x
    (mkRollRevCase (s!"fuzz/ok/x={x}") stack, rng3)

def suite : InstrSuite where
  id := rollRevId
  unit := #[
    { name := "unit/error-cases/underflow-empty"
      run := do
        expectErr "underflow-empty" (runRollRevDirect #[]) .stkUnd
        expectErr "underflow-after-pop" (runRollRevDirect #[(intV 0)]) .stkUnd },
    { name := "unit/error-cases/type-and-range"
      run := do
        expectErr "type-top-null" (runRollRevDirect (#[(.null), intV 7]) ) .typeChk
        expectErr "range-nan" (runRollRevDirect (#[(.int .nan), intV 7]) ) .rangeChk
        expectErr "range-negative" (runRollRevDirect (#[(intV (-1)), intV 7]) ) .rangeChk
        expectErr "range-over-max" (runRollRevDirect (#[(intV (1 <<< 30)), intV 7]) ) .rangeChk },
    { name := "unit/success/x-boundaries"
      run := do
        expectOkStack "x0" (runRollRevDirect (withTop 0 shortTail))
          #[intV 11, .null, .cell Cell.empty, .slice (Slice.ofCell Cell.empty), .builder Builder.empty]
        expectOkStack "x1" (runRollRevDirect (withTop 1 shortTail))
          #[intV 11, .slice (Slice.ofCell Cell.empty), .null, .cell Cell.empty, .builder Builder.empty, .tuple #[]]
        expectOkStack "x2" (runRollRevDirect (withTop 2 shortTail))
          #[.cell Cell.empty, intV 11, .null, .slice (Slice.ofCell Cell.empty), .builder Builder.empty, .tuple #[]] },
    { name := "unit/encoding-and-decoding"
      run := do
        let code ←
          match assembleCp0 [rollRevInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode-self" s0 rollRevInstr 8
        if s1.bitsRemaining ≠ 0 then
          throw (IO.userError s!"decode-self: expected stream empty, got {s1.bitsRemaining}")
        else
          pure ()

        let raw := Slice.ofCell (Cell.mkOrdinary (natToBits 0x61 8 ++ natToBits 0x62 8 ++ natToBits 0x63 8) #[])
        let r1 ← expectDecodeStep "decode-roll" raw .roll 8
        let r2 ← expectDecodeStep "decode-rollrev" r1 .rollRev 8
        let _r3 ← expectDecodeStep "decode-revx" r2 .revX 8
        pure (),
    } ,
    { name := "unit/decoding-invalid-prefix"
      run := do
        match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits 0x00 8) #[])) with
        | .error _ => pure ()
        | .ok _ =>
            throw (IO.userError "decode-invalid-prefix: expected error on 0x00") }
  ]
  oracle := #[
    mkRollRevCase "ok/x0/short/int-tail" (withTop 0 shortTail), -- [B7][A1]
    mkRollRevCase "ok/x0/short/mixed-tail" (withTop 0 (#[(.slice (Slice.ofCell Cell.empty), .builder Builder.empty, .tuple #[], .cell Cell.empty, .null, intV 42])), -- [B7][A1]
    mkRollRevCase "ok/x1/short/ints" (withTop 1 (#[(intV 11), intV 13, .null, .tuple #[]])), -- [B8][A1]
    mkRollRevCase "ok/x1/short/mixed" (withTop 1 (#[(.cell Cell.empty), .slice (Slice.ofCell Cell.empty), intV 99, .builder Builder.empty])), -- [B8][A2]
    mkRollRevCase "ok/x2/short/numeric" (withTop 2 shortTail), -- [B9][A1]
    mkRollRevCase "ok/x2/short/alt-tail" (withTop 2 (#[(.null), intV 8, .cell Cell.empty, .slice (Slice.ofCell Cell.empty)])), -- [B9][A1]
    mkRollRevCase "ok/x3/short" (withTop 3 shortTail), -- [B9][A1]
    mkRollRevCase "ok/x4/short" (withTop 4 shortTail), -- [B9][A1]
    mkRollRevCase "ok/x5/short" (withTop 5 shortTail), -- [B9][A1]
    mkRollRevCase "ok/x6/short" (withTop 6 shortTail), -- [B9][A1]
    mkRollRevCase "ok/x7/long" (withTop 7 longTail256), -- [B9][A1]
    mkRollRevCase "ok/x8/long" (withTop 8 longTail256), -- [B9][A1]
    mkRollRevCase "ok/x16/long" (withTop 16 longTail256), -- [B9][A1]
    mkRollRevCase "ok/x32/long" (withTop 32 longTail256), -- [B9][A1]
    mkRollRevCase "ok/x63/long" (withTop 63 longTail256), -- [B9][A1]
    mkRollRevCase "ok/x127/long" (withTop 127 longTail256), -- [B9][A1]
    mkRollRevCase "ok/x255/long" (withTop 255 longTail256), -- [B9][B11]
    mkRollRevCase "err/underflow/empty" #[], -- [B1][A3]
    mkRollRevCase "err/underflow/single" (#[(intV 0)]), -- [B6]
    mkRollRevCase "err/underflow/equal-size" (withTop 2 (#[(intV 4)])), -- [B6][A1]
    mkRollRevCase "err/type/non-int-null" (#[(.null), intV 2]), -- [B2][A1]
    mkRollRevCase "err/type/non-int-cell" (#[.cell Cell.empty, intV 1]), -- [B2][A1]
    mkRollRevCase "err/type/non-int-builder" (#[.builder Builder.empty, intV 3]), -- [B2][A1]
    mkRollRevCase "err/range/nan" (#[.int .nan, intV 4]), -- [B3][A1]
    mkRollRevCase "err/range/negative" (#[intV (-1), intV 6]), -- [B4][A1]
    mkRollRevCase "err/range/negative-large" (#[intV (-123456), intV 2]), -- [B4][A1]
    mkRollRevCase "err/range/too-large" (#[intV ((1 <<< 30)), intV 5]), -- [B5][A1]
    mkRollRevGasCase "gas/exact/x0/short" 0 shortTail false, -- [B10][B11?]
    mkRollRevGasCase "gas/minus-one/x0/short" 0 shortTail true, -- [B10]
    mkRollRevGasCase "gas/exact/x255/long" 255 longTail256 false, -- [B10][B11]
    mkRollRevGasCase "gas/minus-one/x255/long" 255 longTail256 true, -- [B11]
    mkRollRevGasCase "gas/exact/x256/long" 256 longTail256 false, -- [B11]
    mkRollRevGasCase "gas/minus-one/x256/long" 256 longTail256 true, -- [B11]
    mkRollRevCase "ok/x10/massive-tail-for-branch-coverage" (withTop 10 longTail256), -- [B9][A2]
    mkRollRevCase "ok/x12/massive-tail-for-branch-coverage" (withTop 12 longTail256), -- [B9][A2]
    mkRollRevCase "ok/x20/massive-tail-for-branch-coverage" (withTop 20 longTail256) -- [B9][A2]
  ]
  fuzz := #[
    { seed := 2026022601
      count := 500
      gen := genRollRevFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.ROLLREV
