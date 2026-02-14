import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Dict.DICTIMAX

/-!
INSTRUCTION: DICTIMAX

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch path:
   `execInstrDictDictGetMinMax` is selected for `.dictGetMinMax`; non-matching instruction
   must fall through to `next`.

2. [B2] Preamble checks:
   - `checkUnderflow 2` rejects stacks with fewer than two elements (`.stkUnd`).
   - `popNatUpTo 257` rejects NaN, negative, and values >257 (`.rangeChk`).

3. [B3] Dictionary root pop/type behavior:
   - `.null` is accepted as optional dictionary root (empty).
   - `.cell` is accepted as dictionary root.
   - non-cell/non-null at this position fails with `.typeChk`.

4. [B4] Empty/miss behavior:
   `dictMinMaxWithCells` returns `none`; handler pushes `0`.

5. [B5] Hit behavior:
   For DICTIMAX (`.dictGetMinMax 12`):
   - `byRef=false`, `intKey=true`, `fetchMax=true`, `unsigned=false`.
   - pushes maximum value slice, decoded signed key, and success flag `-1`.

6. [B6] Signed-key width/edge behavior:
   valid `n` values include `0`, `1`, `2`, `8`, `16`, `64`, `128`, `255`, `257`.
   boundary signed keys are exercised (including negative extremes for small widths).

7. [B7] Assembler mapping:
   - accepts args `{2..7}`, `{10..15}`, `{18..23}`, `{26..31}`.
   - `args > 31` -> `.rangeChk`.
   - in-range but gapped args -> `.invOpcode`.

8. [B8] Decoder behavior:
   - boundaries/aliasing:
     `0xf482..0xf487`, `0xf48a..0xf48f`, `0xf492..0xf497`, `0xf49a..0xf49f` decode.
   - gaps `0xf488`, `0xf497`, `0xf4a0`, truncated or partial streams are `.invOpcode`.

9. [B9] Gas:
   this concrete variant does not use remove-byref dynamic penalties;
   fixed base gas plus dictionary traversal validation.
   exact budget succeeds; exact-minus-one fails.

TOTAL BRANCHES: 9
Each oracle case below is tagged with one or more branch IDs.
-/

private def dictIMaxId : InstrId := { name := "DICTIMAX" }

private def dictIMaxInstr : Instr := .dictGetMinMax 12

private def dictIMaxExactGas : Int :=
  computeExactGasBudget dictIMaxInstr

private def dictIMaxExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne dictIMaxInstr

private def dictIMaxGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictIMaxExactGas

private def dictIMaxGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictIMaxExactGasMinusOne

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def sampleValueA : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0xA5 8) #[])
private def sampleValueB : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x5A 8) #[])
private def sampleValueC : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0xC7 8) #[])
private def sampleValueD : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0xD4 8) #[])
private def sampleSlice : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits 0x55 8) #[Cell.empty])
private def fallbackSentinel : Int := 70_101

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some bits => bits
        | none => panic! s!"{label}: invalid signed key={k} for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _, _, _) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root for key={k}, n={n}"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed for key={k}, n={n}: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: dictionary remained empty"

private def dictN0 : Cell :=
  mkDictSetSliceRoot! "DICTIMAX/n=0" 0 #[(0, sampleValueA)]
private def dictN1 : Cell :=
  mkDictSetSliceRoot! "DICTIMAX/n=1" 1 #[(0, sampleValueA), (-1, sampleValueB)]
private def dictN2 : Cell :=
  mkDictSetSliceRoot! "DICTIMAX/n=2" 2 #[(1, sampleValueA), (-2, sampleValueB)]
private def dictN8 : Cell :=
  mkDictSetSliceRoot! "DICTIMAX/n=8" 8 #[(127, sampleValueA), (-128, sampleValueB), (5, sampleValueC)]
private def dictN16 : Cell :=
  mkDictSetSliceRoot! "DICTIMAX/n=16" 16 #[(123, sampleValueA), (-321, sampleValueB)]
private def dictN64 : Cell :=
  mkDictSetSliceRoot! "DICTIMAX/n=64" 64 #[(1, sampleValueA), (0, sampleValueB), (-1, sampleValueC)]
private def dictN128 : Cell :=
  mkDictSetSliceRoot! "DICTIMAX/n=128" 128 #[(7, sampleValueA), (-99, sampleValueB)]
private def dictN255 : Cell :=
  mkDictSetSliceRoot! "DICTIMAX/n=255" 255 #[(1, sampleValueA), (0, sampleValueB), (-3, sampleValueC)]
private def dictN257 : Cell :=
  mkDictSetSliceRoot! "DICTIMAX/n=257" 257 #[(1, sampleValueA), (0, sampleValueB), (-1, sampleValueC)]

private def malformedDictCell : Cell := Cell.mkOrdinary #[] #[]
private def malformedDictCell2 : Cell := Cell.mkOrdinary (natToBits 0b111 3) #[]

private def runDictIMaxDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax (.add) (VM.push (intV fallbackSentinel)) stack

private def runDictIMaxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax dictIMaxInstr stack

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictIMaxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictIMaxId
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
    instr := dictIMaxId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeOk
    (label : String)
    (cell : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .ok (actual, bits, rest) =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {actual}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: decoder did not consume full cell")
  | .error e =>
      throw (IO.userError s!"{label}: decode expected success, got {e}")

private def expectDecodeErr
    (label : String)
    (cell : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {actual}/{bits}")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleErr
    (label : String)
    (instr : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def genDictIMaxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (tag, rng2) := randNat rng1 0 999_999
  let case0 : OracleCase :=
    if shape = 0 then
      mkCase (s!"fuzz/hit/n0/{tag}") #[(.cell dictN0), intV 0]
    else if shape = 1 then
      mkCase (s!"fuzz/hit/n1/{tag}") #[(.cell dictN1), intV 1]
    else if shape = 2 then
      mkCase (s!"fuzz/hit/n2/{tag}") #[(.cell dictN2), intV 2]
    else if shape = 3 then
      mkCase (s!"fuzz/hit/n8/{tag}") #[(.cell dictN8), intV 8]
    else if shape = 4 then
      mkCase (s!"fuzz/hit/n16/{tag}") #[(.cell dictN16), intV 16]
    else if shape = 5 then
      mkCase (s!"fuzz/hit/n64/{tag}") #[(.cell dictN64), intV 64]
    else if shape = 6 then
      mkCase (s!"fuzz/hit/n128/{tag}") #[(.cell dictN128), intV 128]
    else if shape = 7 then
      mkCase (s!"fuzz/hit/n255/{tag}") #[(.cell dictN255), intV 255]
    else if shape = 8 then
      mkCase (s!"fuzz/hit/n257/{tag}") #[(.cell dictN257), intV 257]
    else if shape = 9 then
      mkCase (s!"fuzz/miss/null/{tag}") #[(.null), intV 8]
    else if shape = 10 then
      mkCase (s!"fuzz/miss/null-edge/{tag}") #[(.null), intV 257]
    else if shape = 11 then
      mkCase (s!"fuzz/underflow/empty/{tag}") #[]
    else if shape = 12 then
      mkCase (s!"fuzz/underflow/one/{tag}") #[intV 8]
    else if shape = 13 then
      mkCase (s!"fuzz/err/nan/{tag}") #[(.null), .int .nan]
    else if shape = 14 then
      mkCase (s!"fuzz/err/negative/{tag}") #[(.null), intV (-1)]
    else if shape = 15 then
      mkCase (s!"fuzz/err/too-large/{tag}") #[(.null), intV 999]
    else if shape = 16 then
      mkCase (s!"fuzz/err/root-type-slice/{tag}") #[(.slice sampleSlice), intV 8]
    else if shape = 17 then
      mkCase (s!"fuzz/err/root-type-tuple/{tag}") #[(.tuple #[]), intV 8]
    else if shape = 18 then
      mkCase (s!"fuzz/err/malformed-root/{tag}") #[(.cell malformedDictCell), intV 8]
    else if shape = 19 then
      mkCaseCode (s!"fuzz/decode/f48c/{tag}") (#[(.null), intV 8]) (raw16 0xf48c)
    else if shape = 20 then
      mkCaseCode (s!"fuzz/decode/f488/{tag}") (#[(.null), intV 8]) (raw16 0xf488)
    else if shape = 21 then
      mkCase (s!"fuzz/gas/exact/{tag}") #[(.cell dictN8), intV 8]
        #[.pushInt (.num dictIMaxExactGas), .tonEnvOp .setGasLimit, dictIMaxInstr]
        dictIMaxGasExact
    else
      mkCase (s!"fuzz/gas/exact-minus-one/{tag}") #[(.cell dictN8), intV 8]
        #[.pushInt (.num dictIMaxExactGasMinusOne), .tonEnvOp .setGasLimit, dictIMaxInstr]
        dictIMaxGasExactMinusOne
  ({ name := case0.name, instr := case0.instr, program := case0.program, codeCell? := case0.codeCell?, initStack := case0.initStack, gasLimits := case0.gasLimits, fuel := case0.fuel }, rng2)

def suite : InstrSuite where
  id := dictIMaxId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "fallback"
          (runDictIMaxDispatchFallback #[(.cell dictN8), intV 8])
          #[.cell dictN8, intV 8, intV fallbackSentinel]
    },
    { name := "unit/exec/hit/n0" -- [B2][B3][B5]
      run := do
        expectOkStack "hit/n0"
          (runDictIMaxDirect #[(.cell dictN0), intV 0])
          #[.slice sampleValueA, intV 0, intV (-1)]
    },
    { name := "unit/exec/hit/n1" -- [B6]
      run := do
        expectOkStack "hit/n1"
          (runDictIMaxDirect #[(.cell dictN1), intV 1])
          #[.slice sampleValueA, intV 0, intV (-1)]
    },
    { name := "unit/exec/hit/n2" -- [B6]
      run := do
        expectOkStack "hit/n2"
          (runDictIMaxDirect #[(.cell dictN2), intV 2])
          #[.slice sampleValueA, intV 1, intV (-1)]
    },
    { name := "unit/exec/hit/n8" -- [B5][B6]
      run := do
        expectOkStack "hit/n8"
          (runDictIMaxDirect #[(.cell dictN8), intV 8])
          #[.slice sampleValueA, intV 127, intV (-1)]
    },
    { name := "unit/exec/miss-null" -- [B4]
      run := do
        expectOkStack "miss-null"
          (runDictIMaxDirect #[(.null), intV 8])
          #[intV 0]
    },
    { name := "unit/exec/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDictIMaxDirect #[]) .stkUnd
        expectErr "underflow-one" (runDictIMaxDirect #[intV 8]) .stkUnd
    },
    { name := "unit/exec/n-errors" -- [B2]
      run := do
        expectErr "nan" (runDictIMaxDirect #[(.null), .int .nan]) .rangeChk
        expectErr "negative" (runDictIMaxDirect #[(.null), intV (-1)]) .rangeChk
        expectErr "too-large" (runDictIMaxDirect #[(.null), intV 9999]) .rangeChk
        expectErr "edge-too-large" (runDictIMaxDirect #[(.null), intV 258]) .rangeChk
    },
    { name := "unit/exec/root-type-errors" -- [B3]
      run := do
        expectErr "root-slice" (runDictIMaxDirect #[(.slice sampleSlice), intV 8]) .typeChk
        expectErr "root-tuple" (runDictIMaxDirect #[(.tuple #[]), intV 8]) .typeChk
        expectErr "root-cont" (runDictIMaxDirect #[(.cont (.quit 0)), intV 8]) .typeChk
    },
    { name := "unit/exec/malformed-root" -- [B4]
      run := do
        expectErr "malformed-cell" (runDictIMaxDirect #[(.cell malformedDictCell), intV 8]) .cellUnd
        expectErr "malformed-cell-2" (runDictIMaxDirect #[(.cell malformedDictCell2), intV 8]) .cellUnd
    },
    { name := "unit/asm/ok" -- [B7]
      run := do
        match assembleCp0 [dictIMaxInstr] with
        | .ok c =>
            if c.bits != natToBits 0xf48c 16 then
              throw (IO.userError "assemble encoded wrong opcode for DICTIMAX")
        | .error e =>
            throw (IO.userError s!"assemble failed: {e}")
    },
    { name := "unit/asm/reject-gapped" -- [B7]
      run := do
        expectAssembleErr "assemble-gap-24" (.dictGetMinMax 24) .invOpcode
        expectAssembleErr "assemble-gap-1" (.dictGetMinMax 1) .invOpcode
        expectAssembleErr "assemble-too-large" (.dictGetMinMax 33) .rangeChk
    },
    { name := "unit/decoder/ok-and-neighbor" -- [B8]
      run := do
        expectDecodeOk "decode-f48c" (raw16 0xf48c) (.dictGetMinMax 12)
        expectDecodeOk "decode-f48a" (raw16 0xf48a) (.dictGetMinMax 10)
        expectDecodeOk "decode-f49a" (raw16 0xf49a) (.dictGetMinMax 26)
    },
    { name := "unit/decoder/errors" -- [B8]
      run := do
        expectDecodeErr "decode-f488" (raw16 0xf488) .invOpcode
        expectDecodeErr "decode-f497" (raw16 0xf497) .invOpcode
        expectDecodeErr "decode-f4a0" (raw16 0xf4a0) .invOpcode
        expectDecodeErr "decode-neighbor" (raw16 0xf47f) .invOpcode
        expectDecodeErr "decode-truncated" (raw8 0xf4) .invOpcode
    },
    { name := "unit/exec/gas/exact" -- [B9]
      run := do
        expectOkStack "exact"
          (runDictIMaxDirect #[(.cell dictN8), intV 8])
          #[.slice sampleValueA, intV 127, intV (-1)]
    }
  ]
  oracle := #[
    -- [B2]
    mkCase "oracle/underflow/empty" #[],
    mkCase "oracle/underflow/one-elem" #[intV 8],
    -- [B2]
    mkCase "oracle/n/nan" #[(.null), .int .nan],
    mkCase "oracle/n/zero" #[(.null), intV 0],
    mkCase "oracle/n/one" #[(.null), intV 1],
    mkCase "oracle/n/two" #[(.null), intV 2],
    mkCase "oracle/n/eight" #[(.null), intV 8],
    mkCase "oracle/n/sixteen" #[(.null), intV 16],
    mkCase "oracle/n/sixtyfour" #[(.null), intV 64],
    mkCase "oracle/n/onetwentyeight" #[(.null), intV 128],
    mkCase "oracle/n/twofiftyfive" #[(.null), intV 255],
    mkCase "oracle/n/twofiftyseven" #[(.null), intV 257],
    mkCase "oracle/n/negative" #[(.null), intV (-1)],
    mkCase "oracle/n/too-large" #[(.null), intV 999],
    mkCase "oracle/n/edge" #[(.null), intV 258],
    -- [B3]
    mkCase "oracle/root-type-slice" #[(.slice sampleSlice), intV 8],
    mkCase "oracle/root-type-cont" #[(.cont (.quit 0)), intV 8],
    -- [B4]
    mkCase "oracle/root-malformed-1" #[(.cell malformedDictCell), intV 8],
    mkCase "oracle/root-malformed-2" #[(.cell malformedDictCell2), intV 8],
    -- [B4][B5]
    mkCase "oracle/miss/null/zero" #[(.null), intV 0],
    mkCase "oracle/miss/null/eight" #[(.null), intV 8],
    mkCase "oracle/miss/null/sixteen" #[(.null), intV 16],
    mkCase "oracle/miss/null/sixtyfour" #[(.null), intV 64],
    mkCase "oracle/miss/null/onetwentyeight" #[(.null), intV 128],
    mkCase "oracle/miss/null/twofiftyfive" #[(.null), intV 255],
    mkCase "oracle/miss/null/twofiftyseven" #[(.null), intV 257],
    -- [B5][B6]
    mkCase "oracle/hit/n0" #[(.cell dictN0), intV 0],
    mkCase "oracle/hit/n1" #[(.cell dictN1), intV 1],
    mkCase "oracle/hit/n2" #[(.cell dictN2), intV 2],
    mkCase "oracle/hit/n8" #[(.cell dictN8), intV 8],
    mkCase "oracle/hit/n16" #[(.cell dictN16), intV 16],
    mkCase "oracle/hit/n64" #[(.cell dictN64), intV 64],
    mkCase "oracle/hit/n128" #[(.cell dictN128), intV 128],
    mkCase "oracle/hit/n255" #[(.cell dictN255), intV 255],
    mkCase "oracle/hit/n257" #[(.cell dictN257), intV 257],
    mkCase "oracle/hit/extra-prefix" #[intV 7, .cell dictN8, intV 8],
    mkCase "oracle/hit/two-prefix" #[intV 7, intV 8, .cell dictN8, intV 8],
    -- [B7][B8]
    mkCaseCode "oracle/asm/decode-valid/f48c" #[] (raw16 0xf48c),
    mkCaseCode "oracle/asm/decode-valid/f48f" #[] (raw16 0xf48f),
    mkCaseCode "oracle/asm/decode-valid/f49a" #[] (raw16 0xf49a),
    mkCaseCode "oracle/asm/decode-gapped/f488" #[] (raw16 0xf488),
    mkCaseCode "oracle/asm/decode-gapped/f497" #[] (raw16 0xf497),
    mkCaseCode "oracle/asm/decode-gapped/f4a0" #[] (raw16 0xf4a0),
    mkCaseCode "oracle/asm/decode-truncated" #[] (raw8 0xf4),
    -- [B9]
    mkCase "oracle/gas/exact" #[(.cell dictN8), intV 8]
      (#[.pushInt (.num dictIMaxExactGas), .tonEnvOp .setGasLimit, dictIMaxInstr])
      dictIMaxGasExact,
    mkCase "oracle/gas/exact-minus-one" #[(.cell dictN8), intV 8]
      (#[.pushInt (.num dictIMaxExactGasMinusOne), .tonEnvOp .setGasLimit, dictIMaxInstr])
      dictIMaxGasExactMinusOne
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictIMaxId
      count := 500
      gen := genDictIMaxFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIMAX
