import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTMAX

/-!
INSTRUCTION: DICTMAX

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch path:
   `execInstrDictDictGetMinMax` is selected for `.dictGetMinMax`; any other instruction
   falls back to `next`.

2. [B2] Runtime preconditions:
   - `checkUnderflow 2` rejects stacks with fewer than two elements (`.stkUnd`).
   - `popNatUpTo 1023` rejects non-int, NaN, negative, or too-large `n`.
   - dictionary root pop uses `popMaybeCell`.

3. [B3] Root type behavior:
   - `.null` and `.cell` are accepted dictionary roots.
   - non-null, non-cell values produce `.typeChk` at root pop time.

4. [B4] Miss/malformed traversal:
   - `.null` root returns `[0]`.
   - malformed dictionary cells can fail during traversal (e.g. `.cellUnd`).

5. [B5] Hit behavior:
   - with `fetchMax=true`, `unsigned=true`, `intKey=false`, `byRef=false`,
     a hit pushes `[valueSlice, keySlice, -1]`.
   - root is unchanged as remove flag is false.

6. [B6] `n`-width boundaries:
   valid values include `0`, `1`, `2`, `8`, `16`, `255`, `1023`;
   `1024` must fail at `popNatUpTo`.

7. [B7] Assembler encoding:
   accepts only specific `.dictGetMinMax` arg groups.
   in-range but unsupported args produce `.invOpcode`, out-of-range `>31` produces `.rangeChk`.

8. [B8] Decoder behavior:
   `0xf48a..0xf48f` and `0xf49a..0xf49f` opcodes are accepted (subject to family gaps).
   `0xf488`, `0xf489`, `0xf497`, `0xf4a0`, and truncated bitstreams are rejected.

9. [B9] Gas accounting:
   miss path consumes base gas only;
   hit path additionally consumes `cellCreateGasPrice` for key slice reconstruction.

TOTAL BRANCHES: 9
Each oracle test below is tagged with one or more branch IDs.
-/

private def dictMaxId : InstrId :=
  { name := "DICTMAX" }

private def dictMaxInstr : Instr :=
  .dictGetMinMax 10

private def fallbackSentinel : Int :=
  9_000_001

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def dictMaxExactGas : Int :=
  computeExactGasBudget dictMaxInstr

private def dictMaxExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne dictMaxInstr

private def dictMaxHitGas : Int :=
  dictMaxExactGas + cellCreateGasPrice

private def dictMaxHitGasMinusOne : Int :=
  if dictMaxHitGas > 0 then dictMaxHitGas - 1 else 0

private def dictMaxGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictMaxExactGas

private def dictMaxGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictMaxExactGasMinusOne

private def dictMaxHitGasExact : OracleGasLimits :=
  oracleGasLimitsExact dictMaxHitGas

private def dictMaxHitGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne dictMaxHitGasMinusOne

private def sampleValueA : Slice :=
  mkSliceFromBits (natToBits 0xA5 8)

private def sampleValueB : Slice :=
  mkSliceFromBits (natToBits 0x5A 8)

private def sampleValueC : Slice :=
  mkSliceFromBits (natToBits 0xC7 8)

private def sampleValueD : Slice :=
  mkSliceFromBits (natToBits 0xD4 8)

private def malformedDictCell : Cell :=
  Cell.mkOrdinary #[] #[]

private def malformedDictCell2 : Cell :=
  Cell.mkOrdinary (natToBits 0b111 3) #[]

private def mkKeySlice (n : Nat) (k : Nat) : Slice :=
  mkSliceFromBits (natToBits k n)

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some bits => bits
        | none => panic! s!"{label}: invalid unsigned key {k} for n={n}"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _, _, _) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root while inserting key {k}, n={n}"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed for key {k}, n={n}: {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def dictN0 : Cell :=
  mkDictSetSliceRoot! "DICTMAX/n=0" 0 #[(0, sampleValueA)]

private def dictN1 : Cell :=
  mkDictSetSliceRoot! "DICTMAX/n=1" 1 #[(0, sampleValueA), (1, sampleValueB)]

private def dictN2 : Cell :=
  mkDictSetSliceRoot! "DICTMAX/n=2" 2 #[(0, sampleValueA), (1, sampleValueB), (3, sampleValueC)]

private def dictN8 : Cell :=
  mkDictSetSliceRoot! "DICTMAX/n=8" 8 #[(0x01, sampleValueA), (0x80, sampleValueB), (0xFF, sampleValueC)]

private def dictN16 : Cell :=
  mkDictSetSliceRoot! "DICTMAX/n=16" 16 #[(0x1234, sampleValueA), (0xFFFE, sampleValueB), (0xFFFF, sampleValueC)]

private def dictN255 : Cell :=
  mkDictSetSliceRoot! "DICTMAX/n=255" 255 #[(0, sampleValueA), (1, sampleValueB), (0x7F, sampleValueD)]

private def runDictMaxDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax (.add) (VM.push (intV fallbackSentinel)) stack

private def runDictMaxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax dictMaxInstr stack

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictMaxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictMaxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value := #[])
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictMaxId
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
        throw (IO.userError s!"{label}: decode did not consume full cell")
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

private def genDictMaxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/hit/n0" #[.cell dictN0, intV 0], rng1)
    else if shape = 1 then
      (mkCase "fuzz/hit/n1" #[.cell dictN1, intV 1], rng1)
    else if shape = 2 then
      (mkCase "fuzz/hit/n2" #[.cell dictN2, intV 2], rng1)
    else if shape = 3 then
      (mkCase "fuzz/hit/n8" #[.cell dictN8, intV 8], rng1)
    else if shape = 4 then
      (mkCase "fuzz/hit/n16" #[.cell dictN16, intV 16], rng1)
    else if shape = 5 then
      (mkCase "fuzz/hit/n255" #[.cell dictN255, intV 255], rng1)
    else if shape = 6 then
      (mkCase "fuzz/miss/null/1023" #[.null, intV 1023], rng1)
    else if shape = 7 then
      (mkCase "fuzz/miss/null/257" #[.null, intV 257], rng1)
    else if shape = 8 then
      (mkCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 9 then
      (mkCase "fuzz/underflow/one" #[intV 8], rng1)
    else if shape = 10 then
      (mkCase "fuzz/n/nan" #[.cell dictN8, .int .nan], rng1)
    else if shape = 11 then
      (mkCase "fuzz/n/negative" #[.cell dictN8, intV (-1)], rng1)
    else if shape = 12 then
      (mkCase "fuzz/n/too-large" #[.cell dictN8, intV 1024], rng1)
    else if shape = 13 then
      (mkCase "fuzz/root-type/slice" #[.slice sampleValueA, intV 8], rng1)
    else if shape = 14 then
      (mkCase "fuzz/root-type/tuple" #[.tuple #[], intV 8], rng1)
    else if shape = 15 then
      (mkCase "fuzz/root-type/cont" #[.cont (.quit 0), intV 8], rng1)
    else if shape = 16 then
      (mkCase "fuzz/malformed-root/empty" #[.cell malformedDictCell, intV 8], rng1)
    else if shape = 17 then
      (mkCase "fuzz/malformed-root/prefix" #[.cell malformedDictCell2, intV 8], rng1)
    else if shape = 18 then
      (mkCodeCase "fuzz/decode/f48a" #[.null, intV 8] (raw16 0xf48a), rng1)
    else if shape = 19 then
      (mkCodeCase "fuzz/decode/f488" #[.null, intV 8] (raw16 0xf488), rng1)
    else if shape = 20 then
      (mkCase "fuzz/gas/exact/miss" #[.cell dictN8, intV 8]
        (#[.pushInt (.num dictMaxExactGas), .tonEnvOp .setGasLimit, dictMaxInstr])
        dictMaxGasExact, rng1)
    else if shape = 21 then
      (mkCase "fuzz/gas/exact/minus-one/miss" #[.cell dictN8, intV 8]
        (#[.pushInt (.num dictMaxExactGasMinusOne), .tonEnvOp .setGasLimit, dictMaxInstr])
        dictMaxGasExactMinusOne, rng1)
    else if shape = 22 then
      (mkCase "fuzz/gas/exact/hit" #[.cell dictN8, intV 8]
        (#[.pushInt (.num dictMaxHitGas), .tonEnvOp .setGasLimit, dictMaxInstr])
        dictMaxHitGasExact, rng1)
    else if shape = 23 then
      (mkCase "fuzz/gas/exact/minus-one/hit" #[.cell dictN8, intV 8]
        (#[.pushInt (.num dictMaxHitGasMinusOne), .tonEnvOp .setGasLimit, dictMaxInstr])
        dictMaxHitGasExactMinusOne, rng1)
    else
      (mkCodeCase "fuzz/decode/truncated8" #[.null, intV 8] (raw8 0xf4), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := dictMaxId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "dispatch/fallback"
          (runDictMaxDispatchFallback #[.cell dictN8, intV 8])
          #[.cell dictN8, intV 8, intV fallbackSentinel]
    },
    { name := "unit/encode/ok" -- [B7]
      run := do
        match assembleCp0 [dictMaxInstr] with
        | .ok c =>
            if c.bits != natToBits 0xf48a 16 then
              throw (IO.userError s!"assemble encoded wrong opcode for DICTMAX: {c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble failed: {reprStr e}")
    },
    { name := "unit/encode/reject-lower-gap" -- [B7]
      run := do
        expectAssembleErr "assemble-gap-8" (.dictGetMinMax 8) .invOpcode
        expectAssembleErr "assemble-gap-9" (.dictGetMinMax 9) .invOpcode
    },
    { name := "unit/encode/reject-mid-gap" -- [B7]
      run := do
        expectAssembleErr "assemble-gap-24" (.dictGetMinMax 24) .invOpcode
    },
    { name := "unit/encode/reject-upper" -- [B7]
      run := do
        expectAssembleErr "assemble-upper-32" (.dictGetMinMax 32) .rangeChk
    },
    { name := "unit/decode/ok-boundaries" -- [B8]
      run := do
        expectDecodeOk "decode/f48a" (raw16 0xf48a) (.dictGetMinMax 10)
        expectDecodeOk "decode/f48b" (raw16 0xf48b) (.dictGetMinMax 11)
        expectDecodeOk "decode/f48f" (raw16 0xf48f) (.dictGetMinMax 15)
        expectDecodeOk "decode/f49a" (raw16 0xf49a) (.dictGetMinMax 26)
    },
    { name := "unit/decode/errors" -- [B8]
      run := do
        expectDecodeErr "decode/f488" (raw16 0xf488) .invOpcode
        expectDecodeErr "decode/f489" (raw16 0xf489) .invOpcode
        expectDecodeErr "decode/f497" (raw16 0xf497) .invOpcode
        expectDecodeErr "decode/f4a0" (raw16 0xf4a0) .invOpcode
        expectDecodeErr "decode/truncated" (raw8 0xf4) .invOpcode
    },
    { name := "unit/exec/hit/n0" -- [B5][B6]
      run := do
        expectOkStack "exec/hit/n0"
          (runDictMaxDirect #[.cell dictN0, intV 0])
          #[.slice sampleValueA, .slice (mkKeySlice 0 0), intV (-1)]
    },
    { name := "unit/exec/hit/n1" -- [B5][B6]
      run := do
        expectOkStack "exec/hit/n1"
          (runDictMaxDirect #[.cell dictN1, intV 1])
          #[.slice sampleValueB, .slice (mkKeySlice 1 1), intV (-1)]
    },
    { name := "unit/exec/hit/n2" -- [B5][B6]
      run := do
        expectOkStack "exec/hit/n2"
          (runDictMaxDirect #[.cell dictN2, intV 2])
          #[.slice sampleValueC, .slice (mkKeySlice 2 3), intV (-1)]
    },
    { name := "unit/exec/hit/n8" -- [B5][B6]
      run := do
        expectOkStack "exec/hit/n8"
          (runDictMaxDirect #[.cell dictN8, intV 8])
          #[.slice sampleValueC, .slice (mkKeySlice 8 255), intV (-1)]
    },
    { name := "unit/exec/hit/n16" -- [B5][B6]
      run := do
        expectOkStack "exec/hit/n16"
          (runDictMaxDirect #[.cell dictN16, intV 16])
          #[.slice sampleValueC, .slice (mkKeySlice 16 65535), intV (-1)]
    },
    { name := "unit/exec/miss/null" -- [B4][B6]
      run := do
        expectOkStack "exec/miss/null"
          (runDictMaxDirect #[.null, intV 8])
          #[intV 0]
    },
    { name := "unit/exec/miss/max-n" -- [B4][B6]
      run := do
        expectOkStack "exec/miss/null-max-n"
          (runDictMaxDirect #[.null, intV 1023])
          #[intV 0]
    },
    { name := "unit/exec/underflow/empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDictMaxDirect #[]) .stkUnd
        expectErr "underflow-one" (runDictMaxDirect #[intV 8]) .stkUnd
    },
    { name := "unit/exec/n-errors" -- [B2]
      run := do
        expectErr "n-nan" (runDictMaxDirect #[.null, .int .nan]) .rangeChk
        expectErr "n-negative" (runDictMaxDirect #[.null, intV (-1)]) .rangeChk
        expectErr "n-too-large" (runDictMaxDirect #[.null, intV 1024]) .rangeChk
    },
    { name := "unit/exec/root-type-errors" -- [B3]
      run := do
        expectErr "root-slice" (runDictMaxDirect #[.slice sampleValueA, intV 8]) .typeChk
        expectErr "root-tuple" (runDictMaxDirect #[.tuple #[], intV 8]) .typeChk
        expectErr "root-cont" (runDictMaxDirect #[.cont (.quit 0), intV 8]) .typeChk
    },
    { name := "unit/exec/malformed-root" -- [B4][B9]
      run := do
        expectErr "malformed-empty" (runDictMaxDirect #[.cell malformedDictCell, intV 8]) .cellUnd
        expectErr "malformed-prefix" (runDictMaxDirect #[.cell malformedDictCell2, intV 8]) .cellUnd
    }
  ]
  oracle := #[
    mkCase "oracle/underflow/empty" #[] -- [B2]
    ,
    mkCase "oracle/underflow/one" #[intV 8] -- [B2]
    ,
    mkCase "oracle/n/nan" #[.null, .int .nan] -- [B2]
    ,
    mkCase "oracle/n/zero" #[.null, intV 0] -- [B6]
    ,
    mkCase "oracle/n/one" #[.null, intV 1] -- [B6]
    ,
    mkCase "oracle/n/two" #[.null, intV 2] -- [B6]
    ,
    mkCase "oracle/n/eight" #[.null, intV 8] -- [B6]
    ,
    mkCase "oracle/n/sixteen" #[.null, intV 16] -- [B6]
    ,
    mkCase "oracle/n/two-fifty-five" #[.null, intV 255] -- [B6]
    ,
    mkCase "oracle/n/two-fifty-three" #[.null, intV 1023] -- [B6]
    ,
    mkCase "oracle/n/negative" #[.null, intV (-1)] -- [B2]
    ,
    mkCase "oracle/n/too-large" #[.null, intV 1024] -- [B2]
    ,
    mkCase "oracle/root-type-slice" #[.slice sampleValueA, intV 8] -- [B3]
    ,
    mkCase "oracle/root-type-tuple" #[.tuple #[], intV 8] -- [B3]
    ,
    mkCase "oracle/root-type-cont" #[.cont (.quit 0), intV 8] -- [B3]
    ,
    mkCase "oracle/miss/null/0" #[.null, intV 0] -- [B4]
    ,
    mkCase "oracle/miss/null/8" #[.null, intV 8] -- [B4]
    ,
    mkCase "oracle/miss/null/1023" #[.null, intV 1023] -- [B4]
    ,
    mkCase "oracle/malformed/root-empty" #[.cell malformedDictCell, intV 8] -- [B9]
    ,
    mkCase "oracle/malformed/root-prefix" #[.cell malformedDictCell2, intV 8] -- [B9]
    ,
    mkCase "oracle/hit/n0" #[.cell dictN0, intV 0] -- [B5][B6]
    ,
    mkCase "oracle/hit/n1" #[.cell dictN1, intV 1] -- [B5][B6]
    ,
    mkCase "oracle/hit/n2" #[.cell dictN2, intV 2] -- [B5][B6]
    ,
    mkCase "oracle/hit/n8" #[.cell dictN8, intV 8] -- [B5][B6]
    ,
    mkCase "oracle/hit/n16" #[.cell dictN16, intV 16] -- [B5][B6]
    ,
    mkCase "oracle/hit/n255" #[.cell dictN255, intV 255] -- [B5][B6]
    ,
    mkCodeCase "oracle/decode/ok/f48a" #[.null, intV 8] (raw16 0xf48a) -- [B8]
    ,
    mkCodeCase "oracle/decode/ok/f48b" #[.null, intV 8] (raw16 0xf48b) -- [B8]
    ,
    mkCodeCase "oracle/decode/ok/f48f" #[.null, intV 8] (raw16 0xf48f) -- [B8]
    ,
    mkCodeCase "oracle/decode/ok/f49a" #[.null, intV 8] (raw16 0xf49a) -- [B8]
    ,
    mkCodeCase "oracle/decode/err/f488" #[.null, intV 8] (raw16 0xf488) -- [B8]
    ,
    mkCodeCase "oracle/decode/err/f489" #[.null, intV 8] (raw16 0xf489) -- [B8]
    ,
    mkCodeCase "oracle/decode/err/f497" #[.null, intV 8] (raw16 0xf497) -- [B8]
    ,
    mkCodeCase "oracle/decode/err/f4a0" #[.null, intV 8] (raw16 0xf4a0) -- [B8]
    ,
    mkCodeCase "oracle/decode/err/truncated8" #[.null, intV 8] (raw8 0xf4) -- [B8]
    ,
    mkCase "oracle/gas/exact/miss" #[.cell dictN8, intV 8]
      (#[.pushInt (.num dictMaxExactGas), .tonEnvOp .setGasLimit, dictMaxInstr])
      dictMaxGasExact -- [B9]
    ,
    mkCase "oracle/gas/exact-minus-one/miss" #[.cell dictN8, intV 8]
      (#[.pushInt (.num dictMaxExactGasMinusOne), .tonEnvOp .setGasLimit, dictMaxInstr])
      dictMaxGasExactMinusOne -- [B9]
    ,
    mkCase "oracle/gas/exact/hit" #[.cell dictN8, intV 8]
      (#[.pushInt (.num dictMaxHitGas), .tonEnvOp .setGasLimit, dictMaxInstr])
      dictMaxHitGasExact -- [B9]
    ,
    mkCase "oracle/gas/exact-minus-one/hit" #[.cell dictN8, intV 8]
      (#[.pushInt (.num dictMaxHitGasMinusOne), .tonEnvOp .setGasLimit, dictMaxInstr])
      dictMaxHitGasExactMinusOne -- [B9]
    ,
    mkCase "oracle/hit-255" #[.cell dictN255, intV 255] -- [B5][B6]
    ,
    mkCase "oracle/root-type-int" #[.int (.num 17), intV 8] -- [B3]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictMaxId
      count := 500
      gen := genDictMaxFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTMAX
