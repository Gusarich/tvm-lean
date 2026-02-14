import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Dict.DICTIMIN

/-!
INSTRUCTION: DICTIMIN

Branch map (Lean + C++ reference):

1. [B1] Dispatch branch.
   `.dictGetMinMax` goes through `execInstrDictDictGetMinMax`; others fall through to `next`.
2. [B2] Preamble checks.
   `checkUnderflow 2` and `popNatUpTo 257` (including NaN / negative / too-large cases).
3. [B3] Dictionary value-pop branch.
   `popMaybeCell` accepts `null` and `.cell`, rejects non-cell/non-null.
4. [B4] Miss branch.
   `dictMinMaxWithCells none` pushes only false (`0`).
5. [B5] Hit branch.
   Pushes value slice, key int (signed), then success flag `-1`.
6. [B6] Signed key reconstruction and extremes.
   `bitsToIntSignedTwos` must preserve signed keys for `n=8` and `n=257`.
7. [B7] Dictionary structural errors.
   malformed dict roots must raise `.dictErr`.
8. [B8] Assembler/decoder constraints.
   valid/invalid `dictGetMinMax` args and opcode families, including gap/invalid opcodes and truncation.
9. [B9] Gas accounting.
   exact base budget succeeds, exact-minus-one fails.

TOTAL BRANCHES: 9.
-/

private def suiteId : InstrId := { name := "DICTIMIN" }

private def instr : Instr := .dictGetMinMax 2

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some b => b
        | none =>
            panic! s!"{label}: invalid key ({k}) for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some r, _, _, _) =>
          root := r
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root for ({k})"
      | .error e =>
          panic! s!"{label}: failed to build dict for ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary input"

private def valueA : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 0xA5 8) #[])
private def valueB : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 0x5A 8) #[])
private def valueC : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 0x77 8) #[])

private def dictSingle8 : Cell := mkDictSetSliceRoot! "dictSingle8" 8 #[(0, valueA)]
private def dictTwo8 : Cell := mkDictSetSliceRoot! "dictTwo8" 8 #[(0, valueA), (-1, valueB)]
private def dictThree8 : Cell := mkDictSetSliceRoot! "dictThree8" 8 #[(-1, valueA), (1, valueB), (0, valueC)]

private def dictSingle257 : Cell := mkDictSetSliceRoot! "dictSingle257" 257 #[(0, valueA)]
private def dictTwo257 : Cell := mkDictSetSliceRoot! "dictTwo257" 257 #[(minInt257, valueA), (maxInt257, valueB)]
private def dictThree257 : Cell := mkDictSetSliceRoot! "dictThree257" 257 #[(minInt257, valueA), (0, valueB), (maxInt257, valueC)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def gasExact : OracleGasLimits := oracleGasLimitsExact baseGas
private def gasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne

private def rawOpcodeF482 : Cell := Cell.mkOrdinary (natToBits 0xF482 16) #[]
private def rawOpcodeF483 : Cell := Cell.mkOrdinary (natToBits 0xF483 16) #[]
private def rawOpcodeF484 : Cell := Cell.mkOrdinary (natToBits 0xF484 16) #[]
private def rawOpcodeF485 : Cell := Cell.mkOrdinary (natToBits 0xF485 16) #[]
private def rawOpcodeF486 : Cell := Cell.mkOrdinary (natToBits 0xF486 16) #[]
private def rawOpcodeF487 : Cell := Cell.mkOrdinary (natToBits 0xF487 16) #[]
private def rawOpcodeF489 : Cell := Cell.mkOrdinary (natToBits 0xF489 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def fallbackSentinel : Int := 80_901

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value := #[])
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictIMinDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV fallbackSentinel)) stack

private def runDictIMinDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (actual, 16, rest) =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {actual}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected full decode, left {rest.bitsRemaining}b/{rest.refsRemaining}r")
      else
        pure ()
  | .ok (_, bits, _) =>
      throw (IO.userError s!"{label}: expected 16 bits decoded, got {bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got error {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got success {actual}/{bits}")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def genDictIMinFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/ok/hit/single8" (#[(.cell dictSingle8), intV 8]), rng1)
    else if shape = 1 then
      (mkCase "fuzz/ok/hit/two8" (#[(.cell dictTwo8), intV 8]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/ok/hit/three8" (#[(.cell dictThree8), intV 8]), rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/hit/single257" (#[(.cell dictSingle257), intV 257]), rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/hit/two257" (#[(.cell dictTwo257), intV 257]), rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/hit/three257" (#[(.cell dictThree257), intV 257]), rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/miss/null8" (#[(.null), intV 8]), rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/miss/null16" (#[(.null), intV 16]), rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/miss/null257" (#[(.null), intV 257]), rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/underflow/empty" #[], rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/underflow/one" #[(.null)], rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/type/non-int" (#[(.cell dictTwo8), .null]), rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/type/nan" (#[(.cell dictSingle8), .int .nan]), rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/type/negative-n" (#[(.cell dictSingle8), intV (-1)]), rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/type/n-too-large" (#[(.cell dictSingle8), intV 999]), rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/root/type-non-cell" (#[(.tuple #[]), intV 8]), rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/root/malformed" (#[(.cell malformedDict), intV 8]), rng1)
    else if shape = 17 then
      (mkCaseCode "fuzz/raw/f482" (#[(.null), intV 8]) rawOpcodeF482, rng1)
    else if shape = 18 then
      (mkCaseCode "fuzz/raw/f483" (#[(.null), intV 8]) rawOpcodeF483, rng1)
    else if shape = 19 then
      (mkCaseCode "fuzz/raw/invalid-gap" #[] rawOpcodeF489, rng1)
    else if shape = 20 then
      (mkCase "fuzz/gas/exact" (#[(.null), intV 0])
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
        gasExact, rng1)
    else if shape = 21 then
      (mkCase "fuzz/gas/exact-minus-one" (#[(.null), intV 0])
        (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
        gasExactMinusOne, rng1)
    else
      (mkCaseCode "fuzz/raw/truncated" #[] rawTruncated8, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "fallback" (runDictIMinDispatchFallback #[(.cell dictSingle8), intV 8])
          #[.cell dictSingle8, intV 8, intV fallbackSentinel] },
    { name := "unit/opcode/assemble/valid" -- [B8]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits != natToBits 0xF482 16 then
              throw (IO.userError s!"expected 0xF482, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble valid opcode failed: {reprStr e}") },
    { name := "unit/opcode/assemble/reject-gap" -- [B8]
      run := do
        match assembleCp0 [ExecInstr.dictGetMinMax 1] with
        | .ok _ =>
            throw (IO.userError "assemble accepted invalid args=1")
        | .error _ =>
            pure () },
    { name := "unit/decode/valid-and-truncated" -- [B8]
      run := do
        expectDecodeOk "decode/f482" rawOpcodeF482 (.dictGetMinMax 2)
        expectDecodeOk "decode/f483" rawOpcodeF483 (.dictGetMinMax 3)
        expectDecodeOk "decode/f484" rawOpcodeF484 (.dictGetMinMax 4)
        expectDecodeOk "decode/f485" rawOpcodeF485 (.dictGetMinMax 5)
        expectDecodeOk "decode/f486" rawOpcodeF486 (.dictGetMinMax 6)
        expectDecodeOk "decode/f487" rawOpcodeF487 (.dictGetMinMax 7)
        expectDecodeErr "decode/invalid-gap" rawOpcodeF489 .invOpcode
        expectDecodeErr "decode/truncated-8" rawTruncated8 .invOpcode },
    { name := "unit/exec/hit-and-miss-order" -- [B2][B3][B4][B5][B6]
      run := do
        expectOkStack "direct/hit/single8" (runDictIMinDirect #[(.cell dictSingle8), intV 8]) #[valueA, intV 0, intV (-1)]
        expectOkStack "direct/miss/null" (runDictIMinDirect #[(.null), intV 8]) #[intV 0] }
  ]
  oracle := #[
    mkCase "ok/miss/null/0" (#[(.null), intV 0]), -- [B3][B4]
    mkCase "ok/miss/null/8" (#[(.null), intV 8]), -- [B3][B4]
    mkCase "ok/miss/null/16" (#[(.null), intV 16]), -- [B3][B4]
    mkCase "ok/miss/null/32" (#[(.null), intV 32]), -- [B3][B4]
    mkCase "ok/miss/null/257" (#[(.null), intV 257]), -- [B3][B4]
    mkCase "ok/hit/single8" (#[(.cell dictSingle8), intV 8]), -- [B5][B6]
    mkCase "ok/hit/two8" (#[(.cell dictTwo8), intV 8]), -- [B5][B6]
    mkCase "ok/hit/three8" (#[(.cell dictThree8), intV 8]), -- [B5][B6]
    mkCase "ok/hit/two8/smaller-n" (#[(.cell dictTwo8), intV 2]), -- [B5][B6]
    mkCase "ok/hit/two8/larger-n" (#[(.cell dictTwo8), intV 10]), -- [B5][B6]
    mkCase "ok/hit/single257" (#[(.cell dictSingle257), intV 257]), -- [B5][B6][B7]
    mkCase "ok/hit/two257" (#[(.cell dictTwo257), intV 257]), -- [B5][B6][B7]
    mkCase "ok/hit/three257" (#[(.cell dictThree257), intV 257]), -- [B5][B6][B7]
    mkCase "ok/hit/three257/narrower" (#[(.cell dictThree257), intV 8]), -- [B5][B6][B7]
    mkCaseCode "ok/raw/f482" (#[(.null), intV 8]) rawOpcodeF482, -- [B8]
    mkCaseCode "ok/raw/f483" (#[(.null), intV 8]) rawOpcodeF483, -- [B8]
    mkCaseCode "ok/raw/f484" (#[(.null), intV 8]) rawOpcodeF484, -- [B8]
    mkCaseCode "ok/raw/f485" (#[(.null), intV 8]) rawOpcodeF485, -- [B8]
    mkCaseCode "ok/raw/f486" (#[(.null), intV 8]) rawOpcodeF486, -- [B8]
    mkCaseCode "ok/raw/f487" (#[(.null), intV 8]) rawOpcodeF487, -- [B8]
    mkCase "err/underflow/empty" #[], -- [B2]
    mkCase "err/underflow/one" #[(.null)], -- [B2]
    mkCase "err/type/non-int" (#[(.cell dictSingle8), .null]), -- [B2]
    mkCase "err/type/dict-top-int" (#[.int (.num 7), intV 8]), -- [B3]
    mkCase "err/type/nan" (#[(.cell dictSingle8), .int .nan]), -- [B2]
    mkCase "err/type/negative-n" (#[(.null), intV (-1)]), -- [B2]
    mkCase "err/type/overflow-n" (#[(.null), intV 9999]), -- [B2]
    mkCase "err/root/type-non-cell" (#[(.tuple #[]), intV 8]), -- [B3]
    mkCase "err/root/malformed-small-bits" (#[(.cell malformedDict), intV 8]), -- [B7]
    mkCase "err/mismatch-key-width-short" (#[(.cell dictSingle8), intV 16]), -- [B4]
    mkCase "err/mismatch-key-width-very-long" (#[(.cell dictSingle257), intV 8]), -- [B4]
    mkCase "gas/exact-base-miss" (#[(.null), intV 8])
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      gasExact, -- [B9]
    mkCase "gas/exact-minus-one-miss" (#[(.null), intV 8])
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      gasExactMinusOne, -- [B9]
    mkCaseCode "err/decode/truncated8" #[] rawTruncated8, -- [B8]
    mkCaseCode "err/decode/invalid-gap-489" #[] rawOpcodeF489 -- [B8]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictIMinFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIMIN
