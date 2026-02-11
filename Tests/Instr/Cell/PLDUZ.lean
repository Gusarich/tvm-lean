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

namespace Tests.Instr.Cell.PLDUZ

/-
PLDUZ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.plduz c)`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode `0xd710..0xd717`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`encodeCellExtInstr` currently rejects `.plduz`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_preload_uint_fixed_0e`)

Branch map covered by this suite:
- stack underflow/type on initial `popSlice`;
- width selection from `c`: `bits = 32 * (c + 1)`, for all `c = 0..7`;
- load width clamp: `ldBits = min(bits, s.bitsRemaining)`;
- zero-extension by left shift when `ldBits < bits`;
- stack result order and deep-stack preservation: `... s -> ... s u`;
- decode boundaries around PLDUZ family and dispatch fallback for non-`.plduz`.

Mismatch note:
- assembler path currently does not encode `.cellExt (.plduz c)` and returns `invOpcode`;
  decode and raw-oracle checks still validate the real opcode stream (`0xd710..0xd717`).
-/

private def plduzId : InstrId := { name := "PLDUZ" }

private def dispatchSentinel : Int := 917

private def plduzInstr (c : Nat) : Instr :=
  .cellExt (.plduz c)

private def plduzWord (c : Nat) : Nat :=
  0xd710 + (c &&& 0x7)

private def plduzWidth (c : Nat) : Nat :=
  32 * (c + 1)

private def execInstrCellExtPlduzOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellExt (.plduz _) => execInstrCellExt i next
  | _ => next

private def runPlduzDirect (c : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExtPlduzOnly (plduzInstr c) stack

private def runPlduzDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExtPlduzOnly instr (VM.push (intV dispatchSentinel)) stack

private def stripeBits (n : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := n) fun i => ((i.1 + phase) % 2 = 1)

private def mkPlduzSlice (bits : Nat) (phase : Nat := 0) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase)

private def plduzExpectedNat (c : Nat) (s : Slice) : Nat :=
  let bits : Nat := plduzWidth c
  let ldBits : Nat := Nat.min bits s.bitsRemaining
  (bitsToNat (s.readBits ldBits)) <<< (bits - ldBits)

private def plduzExpectedInt (c : Nat) (s : Slice) : Int :=
  Int.ofNat (plduzExpectedNat c s)

private def plduzModel (c : Nat) (stack : Array Value) : Except Excno (Array Value) := do
  if stack.size = 0 then
    throw .stkUnd
  let top := stack.back!
  match top with
  | .slice s =>
      let below := stack.extract 0 (stack.size - 1)
      pure (below.push (.slice s) |>.push (intV (plduzExpectedInt c s)))
  | _ =>
      throw .typeChk

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 13 4) #[]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 3 2) #[]

private def cursorLongCell : Cell :=
  Cell.mkOrdinary (stripeBits 300 0) #[refLeafA, refLeafB]

private def cursorLongSlice : Slice :=
  { cell := cursorLongCell, bitPos := 37, refPos := 1 }

private def cursorShortCell : Cell :=
  Cell.mkOrdinary (stripeBits 120 1) #[refLeafC]

private def cursorShortSlice : Slice :=
  { cell := cursorShortCell, bitPos := 95, refPos := 0 }

private def mkRaw16ThenAdd (w16 : Nat) : Slice :=
  mkSliceFromBits (natToBits w16 16 ++ natToBits 0xa0 8)

private def ensureExhausted (label : String) (s : Slice) : IO Unit := do
  if s.bitsRemaining = 0 ∧ s.refsRemaining = 0 then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected exhausted slice, got bits={s.bitsRemaining}, refs={s.refsRemaining}")

private structure RawOracleCase where
  name : String
  c : Nat
  initStack : Array Value := #[]
  fuel : Nat := 1_000_000

private def mkRawPlduzCode (c : Nat) : Cell :=
  Cell.mkOrdinary (natToBits (plduzWord c) 16) #[]

private def mkOracleCase
    (name : String)
    (c : Nat)
    (initStack : Array Value)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := plduzId
    codeCell? := some (mkRawPlduzCode c)
    initStack := initStack
    fuel := fuel }

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
      if s.bitPos = 0 && s.refPos = 0 && s.bitsRemaining = s.cell.bits.size && s.refsRemaining = s.cell.refs.size then
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
  let code := mkRawPlduzCode c.c
  let stackTokens ←
    match stackToOracleTokens c.initStack with
    | .ok toks => pure toks
    | .error e => throw (IO.userError s!"{c.name}: {e}")

  let leanCanon ←
    match leanCanonResult (TvmLeanOracleValidate.runLean code c.initStack c.fuel) with
    | .ok result => pure result
    | .error e => throw (IO.userError s!"{c.name}: {e}")

  let oracleOut ←
    try
      TvmLeanOracleValidate.runOracle code stackTokens
    catch e =>
      throw (IO.userError s!"{c.name}: oracle run failed: {e.toString}")

  let oracleCanon :=
    CanonResult.ofOracleRaw oracleOut.exitRaw oracleOut.gasUsed oracleOut.c4Hash oracleOut.c5Hash oracleOut.stackTop
  let cmp := compareCanonResults leanCanon oracleCanon
  if cmp.ok then
    pure ()
  else
    let msg :=
      match cmp.mismatch? with
      | some mismatch => mismatch.message
      | none => "oracle comparison failed"
    throw (IO.userError s!"{c.name}: {msg}")

private def rawOracleExactCases : Array RawOracleCase :=
  (Array.range 8).map fun c =>
    let bits := plduzWidth c
    { name := s!"oracle/ok/exact/c-{c}/w-{bits}"
      c := c
      initStack := #[.slice (mkPlduzSlice bits (c % 2))] }

private def rawOracleShortCases : Array RawOracleCase :=
  (Array.range 8).map fun c =>
    let bits := plduzWidth c
    { name := s!"oracle/ok/short/c-{c}/avail-{bits - 1}"
      c := c
      initStack := #[.slice (mkPlduzSlice (bits - 1) ((c + 1) % 2))] }

private def rawOracleExtraCases : Array RawOracleCase :=
  #[
    { name := "oracle/ok/long/c-0/avail-45/refs-2"
      c := 0
      initStack := #[.slice (mkSliceWithBitsRefs (stripeBits 45 1) #[refLeafA, refLeafB])] },
    { name := "oracle/ok/long/c-3/deep-stack"
      c := 3
      initStack := #[.null, intV 11, .slice (mkPlduzSlice 180 0)] },
    { name := "oracle/ok/long/c-6/deep-stack"
      c := 6
      initStack := #[intV (-5), .null, .slice (mkPlduzSlice 240 1)] },
    { name := "oracle/ok/long/c-7/avail-300/ref-1"
      c := 7
      initStack := #[.slice (mkSliceWithBitsRefs (stripeBits 300 0) #[refLeafC])] }
  ]

private def rawOracleFailCases : Array RawOracleCase :=
  #[
    { name := "oracle/err/underflow/empty"
      c := 0
      initStack := #[] },
    { name := "oracle/err/type/top-null"
      c := 2
      initStack := #[.null] },
    { name := "oracle/err/type/top-int"
      c := 5
      initStack := #[intV 77] },
    { name := "oracle/err/type/deep-top-not-slice"
      c := 7
      initStack := #[.slice (mkPlduzSlice 256 0), .null] }
  ]

private def plduzRawOracleCases : Array RawOracleCase :=
  rawOracleExactCases ++ rawOracleShortCases ++ rawOracleExtraCases ++ rawOracleFailCases

private def plduzRawOracleUnitCases : Array UnitCase :=
  plduzRawOracleCases.map fun c =>
    { name := s!"unit/raw-oracle/{c.name}"
      run := runRawOracleCase c }

private def plduzRawOracleCaseCountMin : Nat := 24

private def plduzRawOracleCaseCountUnit : UnitCase :=
  { name := "unit/raw-oracle/case-count-at-least-24"
    run := do
      if plduzRawOracleUnitCases.size < plduzRawOracleCaseCountMin then
        throw (IO.userError
          s!"raw oracle case count must be at least {plduzRawOracleCaseCountMin}, got {plduzRawOracleUnitCases.size}") }

private def noisePool : Array Value :=
  #[.null, intV 23, .cell refLeafA, .builder Builder.empty]

private def pickNoise (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (noisePool.size - 1)
  (noisePool[idx]!, rng1)

private def pickRefPack (rng0 : StdGen) : Array Cell × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  if pick = 0 then
    (#[refLeafA], rng1)
  else if pick = 1 then
    (#[refLeafA, refLeafB], rng1)
  else
    (#[refLeafA, refLeafB, refLeafC], rng1)

private def pickAvailMixed (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    (0, rng1)
  else if mode = 1 then
    (bits - 1, rng1)
  else if mode = 2 then
    (bits, rng1)
  else if mode = 3 then
    let maxExtra : Nat := Nat.min 192 (1023 - bits)
    let (extra, rng2) := randNat rng1 1 maxExtra
    (bits + extra, rng2)
  else
    let hi : Nat := Nat.min 1023 (bits + 192)
    randNat rng1 0 hi

private def genPlduzFuzzInput (iter : Nat) (rng0 : StdGen) : (Nat × Array Value) × StdGen :=
  let c : Nat := iter % 8
  let bits : Nat := plduzWidth c
  let (shape, rng1) := randNat rng0 0 14
  if shape = 0 then
    ((c, #[.slice (mkPlduzSlice bits (c % 2))]), rng1)
  else if shape = 1 then
    ((c, #[.slice (mkPlduzSlice (bits - 1) ((c + 1) % 2))]), rng1)
  else if shape = 2 then
    let maxDelta : Nat := Nat.min bits 16
    let (delta, rng2) := randNat rng1 1 maxDelta
    ((c, #[.slice (mkPlduzSlice (bits - delta) 1)]), rng2)
  else if shape = 3 then
    let maxExtra : Nat := Nat.min 160 (1023 - bits)
    let (extra, rng2) := randNat rng1 1 maxExtra
    ((c, #[.slice (mkPlduzSlice (bits + extra) 0)]), rng2)
  else if shape = 4 then
    let (avail, rng2) := pickAvailMixed bits rng1
    let (refs, rng3) := pickRefPack rng2
    ((c, #[.slice (mkSliceWithBitsRefs (stripeBits avail (c % 2)) refs)]), rng3)
  else if shape = 5 then
    let (avail, rng2) := pickAvailMixed bits rng1
    let (noise, rng3) := pickNoise rng2
    ((c, #[noise, .slice (mkPlduzSlice avail 1)]), rng3)
  else if shape = 6 then
    let (avail, rng2) := pickAvailMixed bits rng1
    let (noise1, rng3) := pickNoise rng2
    let (noise2, rng4) := pickNoise rng3
    ((c, #[noise1, noise2, .slice (mkPlduzSlice avail 0)]), rng4)
  else if shape = 7 then
    ((c, #[]), rng1)
  else if shape = 8 then
    ((c, #[.null]), rng1)
  else if shape = 9 then
    ((c, #[intV (-3)]), rng1)
  else if shape = 10 then
    ((c, #[.cell refLeafB]), rng1)
  else if shape = 11 then
    ((c, #[.builder Builder.empty]), rng1)
  else if shape = 12 then
    ((c, #[.slice (mkPlduzSlice bits 0), .null]), rng1)
  else if shape = 13 then
    ((c, #[.slice (mkPlduzSlice 0 0)]), rng1)
  else
    let (noise, rng2) := pickNoise rng1
    let s := if c % 2 = 0 then cursorLongSlice else cursorShortSlice
    ((c, #[noise, .slice s]), rng2)

private def plduzFuzzSeed : UInt64 := 2026021049

private def plduzFuzzCount : Nat := 320

private def genPlduzOracleFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (c, rng1) := randNat rng0 0 7
  let bits : Nat := plduzWidth c
  let (shape, rng2) := randNat rng1 0 13
  if shape = 0 then
    (mkOracleCase "fuzz/ok/exact" c #[.slice (mkPlduzSlice bits (c % 2))], rng2)
  else if shape = 1 then
    (mkOracleCase "fuzz/ok/short-minus-one" c #[.slice (mkPlduzSlice (bits - 1) ((c + 1) % 2))], rng2)
  else if shape = 2 then
    let maxDelta : Nat := Nat.min bits 16
    let (delta, rng3) := randNat rng2 1 maxDelta
    (mkOracleCase "fuzz/ok/short-delta" c #[.slice (mkPlduzSlice (bits - delta) 1)], rng3)
  else if shape = 3 then
    let maxExtra : Nat := Nat.min 160 (1023 - bits)
    let (extra, rng3) := randNat rng2 1 maxExtra
    (mkOracleCase "fuzz/ok/long-extra" c #[.slice (mkPlduzSlice (bits + extra) 0)], rng3)
  else if shape = 4 then
    let (avail, rng3) := pickAvailMixed bits rng2
    let (refs, rng4) := pickRefPack rng3
    (mkOracleCase "fuzz/ok/with-refs" c #[.slice (mkSliceWithBitsRefs (stripeBits avail (c % 2)) refs)], rng4)
  else if shape = 5 then
    let (avail, rng3) := pickAvailMixed bits rng2
    let (noise, rng4) := pickNoise rng3
    (mkOracleCase "fuzz/ok/deep-noise" c #[noise, .slice (mkPlduzSlice avail 1)], rng4)
  else if shape = 6 then
    let (avail, rng3) := pickAvailMixed bits rng2
    let (noise1, rng4) := pickNoise rng3
    let (noise2, rng5) := pickNoise rng4
    (mkOracleCase "fuzz/ok/deep-two-noise" c #[noise1, noise2, .slice (mkPlduzSlice avail 0)], rng5)
  else if shape = 7 then
    (mkOracleCase "fuzz/err/underflow-empty" c #[], rng2)
  else if shape = 8 then
    (mkOracleCase "fuzz/err/type-null" c #[.null], rng2)
  else if shape = 9 then
    (mkOracleCase "fuzz/err/type-int" c #[intV 17], rng2)
  else if shape = 10 then
    (mkOracleCase "fuzz/err/type-cell" c #[.cell refLeafB], rng2)
  else if shape = 11 then
    (mkOracleCase "fuzz/err/type-builder" c #[.builder Builder.empty], rng2)
  else if shape = 12 then
    (mkOracleCase "fuzz/err/type-deep-top-not-slice" c #[.slice (mkPlduzSlice bits 0), .null], rng2)
  else
    (mkOracleCase "fuzz/ok/zero-bits-slice" c #[.slice (mkPlduzSlice 0 0)], rng2)

private def plduzBaseUnitCases : Array UnitCase :=
  #[
    { name := "unit/direct/width-min-zeroext-order-and-deep-stack"
      run := do
        for c in [0:8] do
          let bits := plduzWidth c
          let exact := mkPlduzSlice bits (c % 2)
          expectOkStack s!"ok/exact/c-{c}/w-{bits}"
            (runPlduzDirect c #[.slice exact])
            #[.slice exact, intV (plduzExpectedInt c exact)]

          let shortAvail := bits - (c + 1)
          let short := mkPlduzSlice shortAvail ((c + 1) % 2)
          expectOkStack s!"ok/short/c-{c}/avail-{shortAvail}"
            (runPlduzDirect c #[.slice short])
            #[.slice short, intV (plduzExpectedInt c short)]

        let manual := mkSliceFromBits (natToBits 21 5)
        expectOkStack "ok/manual-zeroext/c-0/5-bits"
          (runPlduzDirect 0 #[.slice manual])
          #[.slice manual, intV (Int.ofNat ((21 : Nat) <<< 27))]

        for c in #[0, 3, 7] do
          let bits := plduzWidth c
          let prefBits := stripeBits bits 1
          let tailA := natToBits 0x155 9
          let tailB := natToBits 0x0aa 9
          let sA := mkSliceFromBits (prefBits ++ tailA)
          let sB := mkSliceFromBits (prefBits ++ tailB)
          expectOkStack s!"ok/tail-independent/a/c-{c}"
            (runPlduzDirect c #[.slice sA])
            #[.slice sA, intV (plduzExpectedInt c sA)]
          expectOkStack s!"ok/tail-independent/b/c-{c}"
            (runPlduzDirect c #[.slice sB])
            #[.slice sB, intV (plduzExpectedInt c sB)]

        expectOkStack "ok/partial-cursor/long"
          (runPlduzDirect 7 #[.slice cursorLongSlice])
          #[.slice cursorLongSlice, intV (plduzExpectedInt 7 cursorLongSlice)]

        expectOkStack "ok/partial-cursor/short"
          (runPlduzDirect 2 #[.slice cursorShortSlice])
          #[.slice cursorShortSlice, intV (plduzExpectedInt 2 cursorShortSlice)]

        let deep := mkPlduzSlice 120 0
        expectOkStack "ok/deep-stack-preserved"
          (runPlduzDirect 1 #[.null, intV 42, .slice deep])
          #[.null, intV 42, .slice deep, intV (plduzExpectedInt 1 deep)] }
    ,
    { name := "unit/direct/underflow-and-type-from-popSlice"
      run := do
        expectErr "underflow/empty" (runPlduzDirect 0 #[]) .stkUnd
        expectErr "type/top-null" (runPlduzDirect 1 #[.null]) .typeChk
        expectErr "type/top-int" (runPlduzDirect 2 #[intV 0]) .typeChk
        expectErr "type/top-cell" (runPlduzDirect 3 #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder" (runPlduzDirect 4 #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPlduzDirect 5 #[.slice (mkPlduzSlice 64 0), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-boundary-and-assembler-mismatch"
      run := do
        for c in [0:8] do
          let w := plduzWord c
          let s0 := mkRaw16ThenAdd w
          let s1 ← expectDecodeStep s!"decode/plduz/c-{c}" s0 (plduzInstr c) 16
          let s2 ← expectDecodeStep s!"decode/plduz/c-{c}/tail-add" s1 .add 8
          ensureExhausted s!"decode/plduz/c-{c}/end" s2

        let before := mkRaw16ThenAdd 0xd70f
        let before1 ← expectDecodeStep "decode/boundary/before-plduz-loadint-fixed" before (.loadInt true true true 161) 24
        ensureExhausted "decode/boundary/before-plduz/end" before1

        let after := mkRaw16ThenAdd 0xd718
        let after1 ← expectDecodeStep "decode/boundary/after-plduz-loadslicex" after (.loadSliceX false false) 16
        let after2 ← expectDecodeStep "decode/boundary/after-plduz-tail-add" after1 .add 8
        ensureExhausted "decode/boundary/after-plduz/end" after2

        match assembleCp0 [plduzInstr 0] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/plduz: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/plduz: expected invOpcode, got success")

        let decodedInstr ←
          match decodeCp0WithBits (mkSliceFromBits (natToBits (plduzWord 6) 16)) with
          | .ok (instr, _, _) => pure instr
          | .error e => throw (IO.userError s!"decode/raw/plduz-6 failed: {e}")
        let probe := mkPlduzSlice 211 1
        expectOkStack "decode+exec/plduz-6"
          (runHandlerDirect execInstrCellExt decodedInstr #[.slice probe])
          #[.slice probe, intV (plduzExpectedInt 6 probe)] }
    ,
    { name := "unit/dispatch/non-plduz-falls-through"
      run := do
        expectOkStack "dispatch/non-cellext"
          (runPlduzDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellext"
          (runPlduzDispatchFallback (.cellExt .btos) #[intV (-3)])
          #[intV (-3), intV dispatchSentinel] }
    ,
    { name := "unit/fuzz/targeted-c0-to-c7-320"
      run := do
        if plduzFuzzCount < 240 then
          throw (IO.userError s!"fuzz count must be at least 240, got {plduzFuzzCount}")
        let mut rng := mkStdGen plduzFuzzSeed.toNat
        for i in [0:plduzFuzzCount] do
          let ((c, stack), rng') := genPlduzFuzzInput i rng
          rng := rng'
          let got := runPlduzDirect c stack
          let want := plduzModel c stack
          match got, want with
          | .ok gs, .ok ws =>
              if gs == ws then
                pure ()
              else
                throw (IO.userError
                  s!"fuzz/{i}: stack mismatch\nc={c}\nstack={reprStr stack}\nwant={reprStr want}\ngot={reprStr got}")
          | .error ge, .error we =>
              if ge = we then
                pure ()
              else
                throw (IO.userError
                  s!"fuzz/{i}: error mismatch\nc={c}\nstack={reprStr stack}\nwant={reprStr want}\ngot={reprStr got}")
          | _, _ =>
              throw (IO.userError
                s!"fuzz/{i}: result kind mismatch\nc={c}\nstack={reprStr stack}\nwant={reprStr want}\ngot={reprStr got}") }
  ]

def suite : InstrSuite where
  id := plduzId
  unit := plduzBaseUnitCases ++ #[plduzRawOracleCaseCountUnit] ++ plduzRawOracleUnitCases
  oracle := #[
    -- Branch: `c=0..7`, exact-width slices (no zero-extension).
    mkOracleCase "ok/exact/c-0/w-32" 0 #[.slice (mkPlduzSlice 32 0)],
    mkOracleCase "ok/exact/c-1/w-64" 1 #[.slice (mkPlduzSlice 64 1)],
    mkOracleCase "ok/exact/c-2/w-96" 2 #[.slice (mkPlduzSlice 96 0)],
    mkOracleCase "ok/exact/c-3/w-128" 3 #[.slice (mkPlduzSlice 128 1)],
    mkOracleCase "ok/exact/c-4/w-160" 4 #[.slice (mkPlduzSlice 160 0)],
    mkOracleCase "ok/exact/c-5/w-192" 5 #[.slice (mkPlduzSlice 192 1)],
    mkOracleCase "ok/exact/c-6/w-224" 6 #[.slice (mkPlduzSlice 224 0)],
    mkOracleCase "ok/exact/c-7/w-256" 7 #[.slice (mkPlduzSlice 256 1)],

    -- Branch: `ldBits < bits` (zero-extension by left shift).
    mkOracleCase "ok/short/c-0/avail-31" 0 #[.slice (mkPlduzSlice 31 1)],
    mkOracleCase "ok/short/c-1/avail-63" 1 #[.slice (mkPlduzSlice 63 0)],
    mkOracleCase "ok/short/c-2/avail-95" 2 #[.slice (mkPlduzSlice 95 1)],
    mkOracleCase "ok/short/c-3/avail-127" 3 #[.slice (mkPlduzSlice 127 0)],
    mkOracleCase "ok/short/c-4/avail-159" 4 #[.slice (mkPlduzSlice 159 1)],
    mkOracleCase "ok/short/c-5/avail-191" 5 #[.slice (mkPlduzSlice 191 0)],
    mkOracleCase "ok/short/c-6/avail-223" 6 #[.slice (mkPlduzSlice 223 1)],
    mkOracleCase "ok/short/c-7/avail-255" 7 #[.slice (mkPlduzSlice 255 0)],

    -- Branch: deep-stack preservation and slice refs are preserved.
    mkOracleCase "ok/long/c-0/avail-45/refs-2" 0
      #[.slice (mkSliceWithBitsRefs (stripeBits 45 1) #[refLeafA, refLeafB])],
    mkOracleCase "ok/long/c-3/deep-stack" 3 #[.null, intV 11, .slice (mkPlduzSlice 180 0)],
    mkOracleCase "ok/long/c-6/deep-stack" 6 #[intV (-5), .null, .slice (mkPlduzSlice 240 1)],
    mkOracleCase "ok/long/c-7/avail-300/ref-1" 7
      #[.slice (mkSliceWithBitsRefs (stripeBits 300 0) #[refLeafC])],

    -- Branch: underflow and type-check errors.
    mkOracleCase "err/underflow/empty" 0 #[],
    mkOracleCase "err/type/top-null" 2 #[.null],
    mkOracleCase "err/type/top-int" 5 #[intV 77],
    mkOracleCase "err/type/deep-top-not-slice" 7 #[.slice (mkPlduzSlice 256 0), .null]
  ]
  fuzz := #[
    { seed := 2026021107
      count := 500
      gen := genPlduzOracleFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDUZ
