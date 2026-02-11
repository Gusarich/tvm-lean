import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index
import TvmLean.Validation.Canon.Result
import TvmLean.Validation.Oracle.Report
import TvmLean.Validation.Oracle.Runner

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDBEGINSQ

/-!
SDBEGINSQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/SdBeginsConst.lean` (`.sdBeginsConst quiet pref`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (13-bit const prefix `0xd728>>3`, 8-bit args, inline payload with trailing marker)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.sdBeginsConst ..` is intentionally non-assemblable; `encodeCp0` returns `.invOpcode`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_begins_with_const`, opcodes `SDBEGINS/SDBEGINSQ`).

Branch map covered by this suite:
- dispatch guard (`.sdBeginsConst ..` vs fallback to `next`);
- stack gate for `popSlice` (`stkUnd` / `typeChk`);
- predicate split:
  `s.haveBits(prefLen) && s.readBits(prefLen) == prefBits`;
- quiet success (`SDBEGINSQ`): push advanced slice + status `-1`;
- quiet failure (`SDBEGINSQ`): push original slice + status `0` (no throw);
- non-quiet family boundary (`SDBEGINS`): mismatch throws `.cellUnd`;
- decode boundaries:
  - 14-bit family selectors `0x35ca`/`0x35cb` (non-quiet/quiet),
  - `0xd726`/`0xd727` neighbors (`SDBEGINSX/SDBEGINSXQ`),
  - `invOpcode` on short header / truncated inline payload.
-/

private def sdbeginsqId : InstrId := { name := "SDBEGINSQ" }

private def sdbeginsConstPrefix13 : Nat := 0xd728 >>> 3
private def sdbeginsOpcode14 : Nat := 0x35ca
private def sdbeginsqOpcode14 : Nat := 0x35cb
private def sdbeginsxOpcode : Nat := 0xd726
private def sdbeginsxqOpcode : Nat := 0xd727

private def dispatchSentinel : Int := 13771

private def failUnit (msg : String) : IO α :=
  throw (IO.userError msg)

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun i => ((i.1 + phase) % 2 = 1) || ((i.1 + phase) % 5 = 0)

private def mkFullSlice (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkCursorSlice (pad rem : BitString) (refs : Array Cell := #[]) : Slice :=
  { cell := Cell.mkOrdinary (pad ++ rem) refs
    bitPos := pad.size
    refPos := 0 }

private def mkConstInstr (quiet : Bool) (prefBits : BitString) : Instr :=
  .sdBeginsConst quiet (mkFullSlice prefBits)

private def runSdBeginsConstDirect
    (quiet : Bool)
    (prefBits : BitString)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdBeginsConst (mkConstInstr quiet prefBits) stack

private def runSdBeginsConstDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext
    execInstrCellSdBeginsConst
    instr
    (VM.push (intV dispatchSentinel))
    stack

private def expectedQuietSuccessStack
    (below : Array Value)
    (source : Slice)
    (prefLen : Nat) : Array Value :=
  below ++ #[.slice (source.advanceBits prefLen), intV (-1)]

private def expectedQuietFailureStack
    (below : Array Value)
    (source : Slice) : Array Value :=
  below ++ #[.slice source, intV 0]

private def modelSdBeginsConst
    (quiet : Bool)
    (prefBits : BitString)
    (stack : Array Value) : Except Excno (Array Value) := do
  if stack.size = 0 then
    throw .stkUnd
  let top := stack.back!
  let below := stack.pop
  match top with
  | .slice s =>
      let ok : Bool := s.haveBits prefBits.size && s.readBits prefBits.size == prefBits
      if ok then
        let out := below.push (.slice (s.advanceBits prefBits.size))
        if quiet then
          pure (out.push (intV (-1)))
        else
          pure out
      else if quiet then
        pure ((below.push (.slice s)).push (intV 0))
      else
        throw .cellUnd
  | _ =>
      throw .typeChk

private def expectSameOutcome
    (label : String)
    (lhs rhs : Except Excno (Array Value)) : IO Unit := do
  let same :=
    match lhs, rhs with
    | .ok lv, .ok rv => lv == rv
    | .error le, .error re => le == re
    | _, _ => false
  if same then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected identical outcomes, got lhs={reprStr lhs}, rhs={reprStr rhs}")

private def sdbeginsDataBits (lenTag : Nat) : Nat :=
  lenTag * 8 + 3

private def mkHeaderBits (quiet : Bool) (lenTag : Nat) : BitString :=
  let args8 : Nat := (if quiet then 0x80 else 0) + (lenTag % 128)
  natToBits sdbeginsConstPrefix13 13 ++ natToBits args8 8

private def encodeRawWithMarker (payload : BitString) (lenTag : Nat) : BitString :=
  let dataBits := sdbeginsDataBits lenTag
  if _h : payload.size + 1 ≤ dataBits then
    payload ++ #[true] ++ Array.replicate (dataBits - payload.size - 1) false
  else
    -- Defensive fallback for malformed synthetic inputs.
    #[true]

private def mkRawCodeFromRaw (quiet : Bool) (lenTag : Nat) (raw : BitString) : Cell :=
  Cell.mkOrdinary (mkHeaderBits quiet lenTag ++ raw) #[]

private def mkRawCode (quiet : Bool) (payload : BitString) (lenTag : Nat) : Cell :=
  mkRawCodeFromRaw quiet lenTag (encodeRawWithMarker payload lenTag)

private structure RawOracleCase where
  name : String
  code : Cell
  initStack : Array Value := #[]
  fuel : Nat := 1_000_000

private def toBocHex (c : Cell) : Except String String := do
  let bytes ←
    match stdBocSerialize c with
    | .ok b => pure b
    | .error e => throw s!"stdBocSerialize failed: {reprStr e}"
  pure (TvmLeanOracleValidate.bytesToHex bytes)

private def valueToOracleToken (v : Value) : Except String String := do
  match v with
  | .int (.num n) => pure (toString n)
  | .int .nan => throw "cannot encode NaN in oracle stack token stream"
  | .null => pure "N"
  | .cell c =>
      let hex ← toBocHex c
      pure s!"CB:{hex}"
  | .slice s =>
      if s.bitPos = 0 && s.refPos = 0 && s.bitsRemaining = s.cell.bits.size &&
          s.refsRemaining = s.cell.refs.size then
        let hex ← toBocHex s.cell
        pure s!"SB:{hex}"
      else
        throw "only full-cell slices are supported in oracle stack token stream"
  | .builder b =>
      if b.bits.isEmpty && b.refs.isEmpty then
        pure "B"
      else
        throw "non-empty builders are not yet supported in oracle stack token stream"
  | .tuple t =>
      if t.isEmpty then
        pure "T"
      else
        throw "non-empty tuples are not yet supported in oracle stack token stream"
  | .cont (.quit 0) => pure "K"
  | .cont _ => throw "only quit(0) continuations are supported in oracle stack token stream"

private def stackToOracleTokens (stack : Array Value) : Except String (List String) := do
  let mut out : List String := []
  for v in stack do
    let tok ← valueToOracleToken v
    out := out.concat tok
  pure out

private def leanCanonResult (res : StepResult) : Except String CanonResult := do
  match res with
  | .halt exitCode stF =>
      let (c4Out, c5Out) := TvmLeanOracleValidate.leanOutCells stF
      pure (CanonResult.ofLeanState (~~~ exitCode) stF.gas.gasConsumed c4Out c5Out stF.stack)
  | .continue _ =>
      throw "Lean execution did not halt within fuel"

private def runRawOracleCase (c : RawOracleCase) : IO Unit := do
  let stackTokens ←
    match stackToOracleTokens c.initStack with
    | .ok toks => pure toks
    | .error e => failUnit s!"{c.name}: {e}"

  let leanCanon ←
    match leanCanonResult (TvmLeanOracleValidate.runLean c.code c.initStack c.fuel) with
    | .ok result => pure result
    | .error e => failUnit s!"{c.name}: {e}"

  let oracleOut ←
    try
      TvmLeanOracleValidate.runOracle c.code stackTokens
    catch e =>
      failUnit s!"{c.name}: oracle run failed: {e.toString}"

  let oracleCanon :=
    CanonResult.ofOracleRaw
      oracleOut.exitRaw
      oracleOut.gasUsed
      oracleOut.c4Hash
      oracleOut.c5Hash
      oracleOut.stackTop
  let cmp := compareCanonResults leanCanon oracleCanon
  if cmp.ok then
    pure ()
  else
    let msg :=
      match cmp.mismatch? with
      | some mismatch => mismatch.message
      | none => "oracle comparison failed"
    failUnit s!"{c.name}: {msg}"

private def randBitString (n : Nat) (rng0 : StdGen) : BitString × StdGen := Id.run do
  let mut bits : BitString := #[]
  let mut rng := rng0
  for _ in [0:n] do
    let (bit, rng') := randBool rng
    bits := bits.push bit
    rng := rng'
  return (bits, rng)

private def flipFirstBit (bs : BitString) : BitString :=
  if bs.isEmpty then
    bs
  else
    #[!bs[0]!] ++ bs.extract 1 bs.size

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 77
    else if pick = 2 then .cell (Cell.ofUInt 3 2)
    else .builder Builder.empty
  (v, rng1)

private def prefLenBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127]

private def pickPrefLenMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    let (idx, rng2) := randNat rng1 0 (prefLenBoundaryPool.size - 1)
    (prefLenBoundaryPool[idx]!, rng2)
  else
    randNat rng1 0 127

private def pickRefPack (rng : StdGen) : Array Cell × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let refs :=
    if pick = 0 then #[]
    else if pick = 1 then #[Cell.ofUInt 1 1]
    else #[Cell.ofUInt 1 1, Cell.ofUInt 2 2]
  (refs, rng')

private def genSdbeginsqFuzzInput (rng0 : StdGen) : (BitString × Array Value) × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    let (prefLen, rng2) := pickPrefLenMixed rng1
    let (prefBits, rng3) := randBitString prefLen rng2
    ((prefBits, #[.slice (mkFullSlice prefBits)]), rng3)
  else if shape = 1 then
    let (prefLen, rng2) := pickPrefLenMixed rng1
    let (prefBits, rng3) := randBitString prefLen rng2
    let (tailLen, rng4) := randNat rng3 0 32
    let (tailBits, rng5) := randBitString tailLen rng4
    ((prefBits, #[.slice (mkFullSlice (prefBits ++ tailBits))]), rng5)
  else if shape = 2 then
    let (prefLenRaw, rng2) := pickPrefLenMixed rng1
    let prefLen := if prefLenRaw = 0 then 1 else prefLenRaw
    let (prefBits, rng3) := randBitString prefLen rng2
    ((prefBits, #[.slice (mkFullSlice (flipFirstBit prefBits))]), rng3)
  else if shape = 3 then
    let (prefLenRaw, rng2) := pickPrefLenMixed rng1
    let prefLen := if prefLenRaw = 0 then 1 else prefLenRaw
    let (prefBits, rng3) := randBitString prefLen rng2
    let (shortLen, rng4) := randNat rng3 0 (prefLen - 1)
    let (shortBits, rng5) := randBitString shortLen rng4
    ((prefBits, #[.slice (mkFullSlice shortBits)]), rng5)
  else if shape = 4 then
    let (prefLen, rng2) := pickPrefLenMixed rng1
    let (prefBits, rng3) := randBitString prefLen rng2
    ((prefBits, #[]), rng3)
  else if shape = 5 then
    let (prefLen, rng2) := pickPrefLenMixed rng1
    let (prefBits, rng3) := randBitString prefLen rng2
    ((prefBits, #[.null]), rng3)
  else if shape = 6 then
    let (prefLen, rng2) := pickPrefLenMixed rng1
    let (prefBits, rng3) := randBitString prefLen rng2
    let (n, rng4) := randNat rng3 0 255
    ((prefBits, #[intV (Int.ofNat n)]), rng4)
  else if shape = 7 then
    let (noise, rng2) := pickNoiseValue rng1
    let (prefLen, rng3) := pickPrefLenMixed rng2
    let (prefBits, rng4) := randBitString prefLen rng3
    let (tailLen, rng5) := randNat rng4 0 24
    let (tailBits, rng6) := randBitString tailLen rng5
    ((prefBits, #[noise, .slice (mkFullSlice (prefBits ++ tailBits))]), rng6)
  else if shape = 8 then
    let (noise, rng2) := pickNoiseValue rng1
    let (prefLenRaw, rng3) := pickPrefLenMixed rng2
    let prefLen := if prefLenRaw = 0 then 1 else prefLenRaw
    let (prefBits, rng4) := randBitString prefLen rng3
    ((prefBits, #[noise, .slice (mkFullSlice (flipFirstBit prefBits))]), rng4)
  else if shape = 9 then
    let (prefLen, rng2) := pickPrefLenMixed rng1
    let (prefBits, rng3) := randBitString prefLen rng2
    let (tailLen, rng4) := randNat rng3 0 20
    let (tailBits, rng5) := randBitString tailLen rng4
    let (refs, rng6) := pickRefPack rng5
    ((prefBits, #[.slice (mkFullSlice (prefBits ++ tailBits) refs)]), rng6)
  else if shape = 10 then
    let (prefLenRaw, rng2) := pickPrefLenMixed rng1
    let prefLen := if prefLenRaw = 0 then 1 else prefLenRaw
    let (prefBits, rng3) := randBitString prefLen rng2
    let (refs, rng4) := pickRefPack rng3
    ((prefBits, #[.slice (mkFullSlice (flipFirstBit prefBits) refs)]), rng4)
  else if shape = 11 then
    let (prefLen, rng2) := pickPrefLenMixed rng1
    let (prefBits, rng3) := randBitString prefLen rng2
    let (tailLen, rng4) := randNat rng3 0 16
    let (tailBits, rng5) := randBitString tailLen rng4
    let (padLen, rng6) := randNat rng5 1 5
    let (padBits, rng7) := randBitString padLen rng6
    let (refs, rng8) := pickRefPack rng7
    ((prefBits, #[.slice (mkCursorSlice padBits (prefBits ++ tailBits) refs)]), rng8)
  else if shape = 12 then
    let (prefLenRaw, rng2) := pickPrefLenMixed rng1
    let prefLen := if prefLenRaw = 0 then 1 else prefLenRaw
    let (prefBits, rng3) := randBitString prefLen rng2
    let (tailLen, rng4) := randNat rng3 0 16
    let (tailBits, rng5) := randBitString tailLen rng4
    let (padLen, rng6) := randNat rng5 1 5
    let (padBits, rng7) := randBitString padLen rng6
    ((prefBits, #[.slice (mkCursorSlice padBits (flipFirstBit prefBits ++ tailBits))]), rng7)
  else
    let (prefLen, rng2) := pickPrefLenMixed rng1
    let (prefBits, rng3) := randBitString prefLen rng2
    let (noise1, rng4) := pickNoiseValue rng3
    let (noise2, rng5) := pickNoiseValue rng4
    ((prefBits, #[noise1, noise2, .slice (mkFullSlice prefBits)]), rng5)

private def bitsEmpty : BitString := #[]
private def bits3A : BitString := natToBits 0b101 3
private def bits3B : BitString := natToBits 0b001 3
private def bits6A : BitString := natToBits 0b110101 6
private def bits6MidMismatch : BitString := natToBits 0b111101 6
private def bits8A : BitString := natToBits 0b10110110 8
private def bits8LastMismatch : BitString := natToBits 0b10110111 8
private def bits11A : BitString := stripeBits 11 0
private def bits11Mismatch : BitString := stripeBits 11 1
private def bits13Tail : BitString := natToBits 0x315 13
private def bitsPad4 : BitString := natToBits 0x9 4
private def bitsTail5 : BitString := natToBits 0x16 5

private def refLeafB : Cell := Cell.mkOrdinary (natToBits 11 4) #[]

private def sliceEmpty : Slice := mkFullSlice bitsEmpty
private def slice3A : Slice := mkFullSlice bits3A
private def slice3B : Slice := mkFullSlice bits3B
private def slice8A : Slice := mkFullSlice bits8A
private def slice8WithPref3 : Slice := mkFullSlice (bits3A ++ natToBits 0x1f 5)
private def slice24WithPref11 : Slice := mkFullSlice (bits11A ++ bits13Tail)
private def sliceSourceRefs : Slice := mkFullSlice (bits11A ++ bitsTail5) #[refLeafA, refLeafB]
private def sliceShort4 : Slice := mkFullSlice (natToBits 0xa 4)
private def slice6MidMismatch : Slice := mkFullSlice bits6MidMismatch
private def slice8LastMismatch : Slice := mkFullSlice bits8LastMismatch
private def sliceCursorMatch : Slice := mkCursorSlice bitsPad4 (bits11A ++ bitsTail5) #[refLeafA]
private def sliceCursorMismatch : Slice := mkCursorSlice bitsPad4 (bits11Mismatch ++ bitsTail5) #[refLeafA]

private def markerlessRawLen0 : BitString :=
  Array.replicate (sdbeginsDataBits 0) false

private def truncatedPayloadRawLen1 : BitString :=
  (encodeRawWithMarker bits3A 1).take 10

private def payloadLen1Max10 : BitString :=
  stripeBits 10 1

private def codeHeaderTooShort : Cell :=
  Cell.mkOrdinary ((mkHeaderBits true 0).take 20) #[]

private def codeTruncatedPayload : Cell :=
  mkRawCodeFromRaw true 1 truncatedPayloadRawLen1

private def codeMarkerlessLen0 : Cell :=
  mkRawCodeFromRaw true 0 markerlessRawLen0

private def rawOracleCases : Array RawOracleCase :=
  #[
    { name := "ok/quiet-empty-on-empty"
      code := mkRawCode true bitsEmpty 0
      initStack := #[.slice sliceEmpty] },
    { name := "ok/quiet-empty-on-nonempty"
      code := mkRawCode true bitsEmpty 0
      initStack := #[.slice slice8A] },
    { name := "ok/quiet-exact-3"
      code := mkRawCode true bits3A 1
      initStack := #[.slice slice3A] },
    { name := "ok/quiet-prefix-3-of-8"
      code := mkRawCode true bits3A 1
      initStack := #[.slice slice8WithPref3] },
    { name := "ok/quiet-prefix-11-of-24"
      code := mkRawCode true bits11A 2
      initStack := #[.slice slice24WithPref11] },
    { name := "ok/quiet-source-with-refs"
      code := mkRawCode true bits11A 2
      initStack := #[.slice sliceSourceRefs] },
    { name := "ok/quiet-deep-stack-preserved"
      code := mkRawCode true bits3A 1
      initStack := #[.null, intV 19, .slice slice8WithPref3] },

    { name := "fail/quiet-prefix-longer-than-source"
      code := mkRawCode true bits8A 1
      initStack := #[.slice slice3A] },
    { name := "fail/quiet-mismatch-first"
      code := mkRawCode true bits3A 1
      initStack := #[.slice slice3B] },
    { name := "fail/quiet-mismatch-middle"
      code := mkRawCode true bits6A 1
      initStack := #[.slice slice6MidMismatch] },
    { name := "fail/quiet-mismatch-last"
      code := mkRawCode true bits8A 1
      initStack := #[.slice slice8LastMismatch] },
    { name := "fail/quiet-nonempty-vs-empty"
      code := mkRawCode true bits3A 1
      initStack := #[.slice sliceEmpty] },
    { name := "fail/quiet-deep-stack-preserved"
      code := mkRawCode true bits3A 1
      initStack := #[.null, intV 21, .slice slice3B] },

    { name := "err/underflow-empty"
      code := mkRawCode true bits3A 1
      initStack := #[] },
    { name := "err/type-top-null"
      code := mkRawCode true bits3A 1
      initStack := #[.null] },
    { name := "err/type-top-int"
      code := mkRawCode true bits3A 1
      initStack := #[intV 7] },
    { name := "err/type-top-cell"
      code := mkRawCode true bits3A 1
      initStack := #[.cell refLeafA] },

    { name := "ok/nonquiet-success-no-status"
      code := mkRawCode false bits3A 1
      initStack := #[.slice slice8WithPref3] },
    { name := "err/nonquiet-failure-cellund"
      code := mkRawCode false bits3A 1
      initStack := #[.slice slice3B] },

    { name := "decode/markerless-raw-empty-prefix"
      code := codeMarkerlessLen0
      initStack := #[.slice slice8A] },
    { name := "decode/truncated-header-invopcode"
      code := codeHeaderTooShort
      initStack := #[.slice slice8A] },
    { name := "ok/quiet-len1-max-payload-10"
      code := mkRawCode true payloadLen1Max10 1
      initStack := #[.slice (mkFullSlice (payloadLen1Max10 ++ bitsTail5))] },
    { name := "ok/quiet-large-len124-empty-prefix"
      code := mkRawCode true bitsEmpty 124
      initStack := #[.slice slice8A] }
  ]

private def rawOracleUnitCases : Array UnitCase :=
  rawOracleCases.map fun c =>
    { name := s!"unit/raw-oracle/{c.name}"
      run := runRawOracleCase c }

private def baseUnitCases : Array UnitCase :=
  #[
    { name := "unit/direct/quiet-success-equal-proper-empty"
      run := do
        let checks : Array (String × BitString × Slice) :=
          #[
            ("ok/empty-prefix-empty-source", bitsEmpty, sliceEmpty),
            ("ok/empty-prefix-nonempty-source", bitsEmpty, slice8A),
            ("ok/exact-3", bits3A, slice3A),
            ("ok/proper-prefix-3-of-8", bits3A, slice8WithPref3),
            ("ok/proper-prefix-11-of-24", bits11A, slice24WithPref11)
          ]
        for (label, prefBits, source) in checks do
          expectOkStack label
            (runSdBeginsConstDirect true prefBits #[.slice source])
            (expectedQuietSuccessStack #[] source prefBits.size) }
    ,
    { name := "unit/direct/quiet-failure-preserve-source-status"
      run := do
        let checks : Array (String × BitString × Slice) :=
          #[
            ("fail/prefix-longer-than-source", bits8A, slice3A),
            ("fail/mismatch-first-bit", bits3A, slice3B),
            ("fail/mismatch-middle-bit", bits6A, slice6MidMismatch),
            ("fail/mismatch-last-bit", bits8A, slice8LastMismatch),
            ("fail/nonempty-prefix-vs-empty-source", bits3A, sliceEmpty)
          ]
        for (label, prefBits, source) in checks do
          expectOkStack label
            (runSdBeginsConstDirect true prefBits #[.slice source])
            (expectedQuietFailureStack #[] source) }
    ,
    { name := "unit/direct/cursor-refs-and-deep-stack"
      run := do
        expectOkStack "ok/source-refs-ignored"
          (runSdBeginsConstDirect true bits11A #[.slice sliceSourceRefs])
          (expectedQuietSuccessStack #[] sliceSourceRefs bits11A.size)

        expectOkStack "ok/cursor-prefix-match"
          (runSdBeginsConstDirect true bits11A #[.slice sliceCursorMatch])
          (expectedQuietSuccessStack #[] sliceCursorMatch bits11A.size)

        expectOkStack "fail/cursor-prefix-mismatch"
          (runSdBeginsConstDirect true bits11A #[.slice sliceCursorMismatch])
          (expectedQuietFailureStack #[] sliceCursorMismatch)

        expectOkStack "ok/deep-stack-preserved"
          (runSdBeginsConstDirect true bits3A #[.null, intV 99, .slice slice8WithPref3])
          (expectedQuietSuccessStack #[.null, intV 99] slice8WithPref3 bits3A.size)

        expectOkStack "fail/deep-stack-preserved"
          (runSdBeginsConstDirect true bits3A #[.null, intV 99, .slice slice3B])
          (expectedQuietFailureStack #[.null, intV 99] slice3B) }
    ,
    { name := "unit/direct/underflow-type-and-nonquiet-contrast"
      run := do
        expectErr "underflow/empty-stack"
          (runSdBeginsConstDirect true bits3A #[]) .stkUnd
        expectErr "type/top-null"
          (runSdBeginsConstDirect true bits3A #[.null]) .typeChk
        expectErr "type/top-int"
          (runSdBeginsConstDirect true bits3A #[intV 1]) .typeChk
        expectErr "type/top-cell"
          (runSdBeginsConstDirect true bits3A #[.cell refLeafA]) .typeChk
        expectErr "type/top-builder"
          (runSdBeginsConstDirect true bits3A #[.builder Builder.empty]) .typeChk

        expectErr "nonquiet/mismatch-throws-cellund"
          (runSdBeginsConstDirect false bits3A #[.slice slice3B]) .cellUnd

        expectOkStack "nonquiet/success-no-status-pushed"
          (runSdBeginsConstDirect false bits3A #[.slice slice8WithPref3])
          #[.slice (slice8WithPref3.advanceBits bits3A.size)] }
    ,
    { name := "unit/model/alignment-representative-quiet-and-nonquiet"
      run := do
        let samples : Array (String × Bool × BitString × Array Value) :=
          #[
            ("quiet/ok/empty-prefix", true, bitsEmpty, #[.slice slice8A]),
            ("quiet/ok/exact", true, bits3A, #[.slice slice3A]),
            ("quiet/fail/mismatch", true, bits3A, #[.slice slice3B]),
            ("quiet/fail/short", true, bits8A, #[.slice slice3A]),
            ("quiet/type", true, bits3A, #[.null]),
            ("quiet/underflow", true, bits3A, #[]),
            ("nonquiet/ok/proper-prefix", false, bits3A, #[.slice slice8WithPref3]),
            ("nonquiet/fail/cellund", false, bits3A, #[.slice slice3B]),
            ("nonquiet/type", false, bits3A, #[intV 11]),
            ("nonquiet/underflow", false, bits3A, #[])
          ]
        for (label, quiet, prefBits, stack) in samples do
          expectSameOutcome s!"model/{label}"
            (runSdBeginsConstDirect quiet prefBits stack)
            (modelSdBeginsConst quiet prefBits stack) }
    ,
    { name := "unit/opcode/decode-family-boundaries"
      run := do
        let nonQuiet14 := bitsToNat ((mkHeaderBits false 0).extract 0 14)
        if nonQuiet14 = sdbeginsOpcode14 then
          pure ()
        else
          failUnit s!"opcode/nonquiet14: expected {sdbeginsOpcode14}, got {nonQuiet14}"

        let quiet14 := bitsToNat ((mkHeaderBits true 0).extract 0 14)
        if quiet14 = sdbeginsqOpcode14 then
          pure ()
        else
          failUnit s!"opcode/quiet14: expected {sdbeginsqOpcode14}, got {quiet14}"

        let addCell ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => failUnit s!"assemble/add failed: {e}"

        let rawBits : BitString :=
          natToBits sdbeginsxOpcode 16 ++
          natToBits sdbeginsxqOpcode 16 ++
          mkHeaderBits false 1 ++ encodeRawWithMarker bits3A 1 ++
          mkHeaderBits true 1 ++ encodeRawWithMarker bits3A 1 ++
          addCell.bits
        let s0 := mkSliceFromBits rawBits
        let s1 ← expectDecodeStep "decode/sdbeginsx-0xd726" s0 (.sdBeginsX false) 16
        let s2 ← expectDecodeStep "decode/sdbeginsxq-0xd727" s1 (.sdBeginsX true) 16
        let s3 ← expectDecodeStep "decode/sdbegins-const-quiet0" s2 (mkConstInstr false bits3A) 21
        let s4 ← expectDecodeStep "decode/sdbeginsq-const-quiet1" s3 (mkConstInstr true bits3A) 21
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining" }
    ,
    { name := "unit/opcode/decode-truncation-markerless-and-len1-max"
      run := do
        match decodeCp0WithBits (Slice.ofCell codeHeaderTooShort) with
        | .error .invOpcode => pure ()
        | .error e => failUnit s!"decode/short-header: expected invOpcode, got {e}"
        | .ok (instr, bits, _) =>
            failUnit s!"decode/short-header: expected failure, got instr={reprStr instr} bits={bits}"

        match decodeCp0WithBits (Slice.ofCell codeTruncatedPayload) with
        | .error .invOpcode => pure ()
        | .error e => failUnit s!"decode/truncated-payload: expected invOpcode, got {e}"
        | .ok (instr, bits, _) =>
            failUnit s!"decode/truncated-payload: expected failure, got instr={reprStr instr} bits={bits}"

        let s0 := Slice.ofCell codeMarkerlessLen0
        let s1 ← expectDecodeStep "decode/markerless-len0" s0 (mkConstInstr true bitsEmpty) 21
        if s1.bitsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/markerless-end: expected exhausted slice, got {s1.bitsRemaining} bits"

        let maxPayloadCode := mkRawCode true payloadLen1Max10 1
        let s2 ← expectDecodeStep "decode/len1-maxpayload10" (Slice.ofCell maxPayloadCode)
          (mkConstInstr true payloadLen1Max10) 21
        if s2.bitsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/len1-maxpayload10-end: expected exhausted slice, got {s2.bitsRemaining} bits" }
    ,
    { name := "unit/opcode/assemble-reject-and-dispatch"
      run := do
        match assembleCp0 [mkConstInstr true bits3A] with
        | .error .invOpcode => pure ()
        | .error e => failUnit s!"assemble/sdbeginsq-const: expected invOpcode, got {e}"
        | .ok _ => failUnit "assemble/sdbeginsq-const: expected invOpcode, got success"

        match assembleCp0 [mkConstInstr false bits3A] with
        | .error .invOpcode => pure ()
        | .error e => failUnit s!"assemble/sdbegins-const: expected invOpcode, got {e}"
        | .ok _ => failUnit "assemble/sdbegins-const: expected invOpcode, got success"

        let xCode ←
          match assembleCp0 [(.sdBeginsX false), (.sdBeginsX true)] with
          | .ok c => pure c
          | .error e => failUnit s!"assemble/sdbeginsx-and-sdbeginsxq failed: {e}"
        let expectedBits := natToBits sdbeginsxOpcode 16 ++ natToBits sdbeginsxqOpcode 16
        if xCode.bits = expectedBits then
          pure ()
        else
          failUnit s!"assemble/sdbeginsx-and-sdbeginsxq: expected {expectedBits}, got {xCode.bits}"

        expectOkStack "dispatch/add-falls-through"
          (runSdBeginsConstDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/sdbeginsxq-falls-through"
          (runSdBeginsConstDispatchFallback (.sdBeginsX true) #[.slice slice8A])
          #[.slice slice8A, intV dispatchSentinel] }
  ]

private def fuzzUnitCases : Array UnitCase :=
  #[
    { name := "unit/fuzz/seeded-model-320"
      run := do
        let mut rng := mkStdGen 2026021025
        for i in [0:320] do
          let ((prefBits, stack), rng') := genSdbeginsqFuzzInput rng
          rng := rng'
          expectSameOutcome s!"fuzz/{i}"
            (runSdBeginsConstDirect true prefBits stack)
            (modelSdBeginsConst true prefBits stack) }
  ]

def suite : InstrSuite where
  id := sdbeginsqId
  unit := baseUnitCases ++ rawOracleUnitCases ++ fuzzUnitCases
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDBEGINSQ
