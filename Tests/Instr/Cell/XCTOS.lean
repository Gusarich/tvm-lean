import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.XCTOS

/-
XCTOS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Xctos.lean` (`.xctos`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.xctos` encodes to `0xd739`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd739` decodes to `.xctos`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_cell_to_slice_maybe_special`, opcode `0xd739`)
  - `/Users/daniil/Coding/ton/crypto/vm/cells/CellSlice.cpp`
    (`load_cell_slice_ref_special`: special cells are accepted and reported via bool).

Branch map covered by this suite:
- dispatch guard (`.xctos` vs fallback `next`);
- top pop via `VM.popCell` (`stkUnd` / `typeChk` / success);
- cell-load accounting branch (`cellLoadGasPrice` for first load, `cellReloadGasPrice` if cached);
- success split by `c.special` flag (`0` for ordinary, `-1` for special);
- opcode/decode boundaries around `0xd739` with neighbors (`0xd737`, `0xd73a`, `0xd73b`) and decode gap `0xd738`.
-/

private def xctosId : InstrId := { name := "XCTOS" }

private def xctosInstr : Instr := .xctos

private def ctosInstr : Instr := .ctos

private def splitInstr : Instr := .cellOp (.split false)

private def splitQInstr : Instr := .cellOp (.split true)

private def xloadInstr : Instr := .cellExt (.xload false)

private def xloadQInstr : Instr := .cellExt (.xload true)

private def xctosOpcode : Nat := 0xd739

private def ctosOpcode : Nat := 0xd0

private def dispatchSentinel : Int := 739

private def mkXctosCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[xctosInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xctosId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runXctosDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellXctos xctosInstr stack

private def runXctosDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellXctos instr (VM.push (intV dispatchSentinel)) stack

private def runXctosRaw
    (stack : Array Value)
    (loadedCells : Array (Array UInt8) := #[]) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, loadedCells := loadedCells }
  let (res, st1) := (execInstrCellXctos xctosInstr (pure ())).run st0
  (res, st1)

private def expectDecodeErr
    (label : String)
    (s : Slice)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def gasForInstrWithFallback (instr : Instr) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok budget => budget
  | .error _ => instrGas instr 16

private def setGasNeedForInstrWithExtra (instr : Instr) (n : Int) (extra : Int) : Int :=
  gasForInstrWithFallback (.pushInt (.num n))
    + gasForInstrWithFallback (.tonEnvOp .setGasLimit)
    + gasForInstrWithFallback instr
    + implicitRetGasPrice
    + extra

private def exactGasBudgetFixedPointWithExtra (instr : Instr) (n : Int) (extra : Int) : Nat → Int
  | 0 => n
  | k + 1 =>
      let n' := setGasNeedForInstrWithExtra instr n extra
      if n' = n then n else exactGasBudgetFixedPointWithExtra instr n' extra k

private def computeExactGasBudgetWithExtra (instr : Instr) (extra : Int) : Int :=
  exactGasBudgetFixedPointWithExtra instr 64 extra 20

private def xctosSetGasExact : Int :=
  -- XCTOS charges registerCellLoad before pushing (slice, special-flag).
  computeExactGasBudgetWithExtra xctosInstr cellLoadGasPrice

private def xctosSetGasExactMinusOne : Int :=
  if xctosSetGasExact > 0 then xctosSetGasExact - 1 else 0

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun i => ((i.1 + phase) % 2 = 1)

private def mkSpecialLibraryCell (phase : Nat) : Cell :=
  { bits := natToBits 2 8 ++ stripeBits 256 phase
    refs := #[]
    special := true
    levelMask := 0 }

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0b101 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x2A 6) #[refLeafA]

private def refLeafC : Cell :=
  Cell.mkOrdinary (stripeBits 9 1) #[refLeafA, Cell.empty]

private def refLeafD : Cell :=
  Cell.mkOrdinary (stripeBits 4 2) #[refLeafB]

private def ordinaryRefPool : Array Cell :=
  #[refLeafA, refLeafB, refLeafC, refLeafD, Cell.empty]

private def cOrdEmpty : Cell := Cell.empty

private def cOrdBits7 : Cell := Cell.ofUInt 7 0x55

private def cOrdBits255 : Cell := Cell.mkOrdinary (stripeBits 255 1) #[]

private def cOrdRefs1 : Cell := Cell.mkOrdinary (stripeBits 5 0) #[refLeafA]

private def cOrdRefs4 : Cell := Cell.mkOrdinary (stripeBits 17 2) #[refLeafA, refLeafB, refLeafC, refLeafD]

private def cOrdBits1023 : Cell := Cell.mkOrdinary (stripeBits 1023 3) #[]

private def cOrdNested : Cell := Cell.mkOrdinary (stripeBits 33 1) #[refLeafB, refLeafC]

private def specialLibraryCellA : Cell := mkSpecialLibraryCell 0

private def specialLibraryCellB : Cell := mkSpecialLibraryCell 1

private def specialCellPool : Array Cell :=
  #[specialLibraryCellA, specialLibraryCellB]

private def expectedXctosStack (below : Array Value) (c : Cell) : Array Value :=
  below ++ #[.slice (Slice.ofCell c), intV (if c.special then -1 else 0)]

private def xctosBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 63, 64, 127, 255, 256, 511, 1023]

private def pickBitsLenBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (xctosBitsBoundaryPool.size - 1)
  (xctosBitsBoundaryPool[idx]!, rng')

private def pickBitsLenMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    pickBitsLenBoundary rng1
  else
    randNat rng1 0 1023

private def pickPatternBits (rng0 : StdGen) : BitString × StdGen :=
  let (len, rng1) := pickBitsLenMixed rng0
  let (phase, rng2) := randNat rng1 0 3
  (stripeBits len phase, rng2)

private def genRefArray (count : Nat) (rng0 : StdGen) : Array Cell × StdGen := Id.run do
  let mut refs : Array Cell := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (idx, rng') := randNat rng 0 (ordinaryRefPool.size - 1)
    refs := refs.push (ordinaryRefPool[idx]!)
    rng := rng'
  return (refs, rng)

private def genOrdinaryCell (rng0 : StdGen) : Cell × StdGen :=
  let (bits, rng1) := pickPatternBits rng0
  let (refCount, rng2) := randNat rng1 0 4
  let (refs, rng3) := genRefArray refCount rng2
  (Cell.mkOrdinary bits refs, rng3)

private def pickSpecialCell (rng0 : StdGen) : Cell × StdGen :=
  let (idx, rng1) := randNat rng0 0 (specialCellPool.size - 1)
  (specialCellPool[idx]!, rng1)

private def pickNoise (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV (-7)
    else if pick = 2 then .builder Builder.empty
    else .tuple #[]
  (v, rng1)

private def pickNonCellTop (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 19
    else if pick = 2 then .slice (Slice.ofCell Cell.empty)
    else if pick = 3 then .builder Builder.empty
    else .tuple #[]
  (v, rng1)

private def genXctosFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  if shape = 0 then
    (mkXctosCase "fuzz/ok/top/ordinary-empty" #[.cell cOrdEmpty], rng1)
  else if shape = 1 then
    let (c, rng2) := genOrdinaryCell rng1
    (mkXctosCase s!"fuzz/ok/top/ordinary/bits-{c.bits.size}/refs-{c.refs.size}" #[.cell c], rng2)
  else if shape = 2 then
    let (c, rng2) := pickSpecialCell rng1
    (mkXctosCase "fuzz/ok/top/special-library" #[.cell c], rng2)
  else if shape = 3 then
    let (c, rng2) := genOrdinaryCell rng1
    let (noise, rng3) := pickNoise rng2
    (mkXctosCase s!"fuzz/ok/deep/ordinary/bits-{c.bits.size}/refs-{c.refs.size}" #[noise, .cell c], rng3)
  else if shape = 4 then
    let (c, rng2) := pickSpecialCell rng1
    let (noise, rng3) := pickNoise rng2
    (mkXctosCase "fuzz/ok/deep/special-library" #[noise, .cell c], rng3)
  else if shape = 5 then
    (mkXctosCase "fuzz/ok/top/ordinary-max-1023" #[.cell cOrdBits1023], rng1)
  else if shape = 6 then
    (mkXctosCase "fuzz/ok/top/ordinary-refs4" #[.cell cOrdRefs4], rng1)
  else if shape = 7 then
    (mkXctosCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 8 then
    (mkXctosCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 9 then
    (mkXctosCase "fuzz/type/top-int" #[intV 0], rng1)
  else if shape = 10 then
    (mkXctosCase "fuzz/type/top-slice" #[.slice (Slice.ofCell Cell.empty)], rng1)
  else if shape = 11 then
    (mkXctosCase "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else if shape = 12 then
    (mkXctosCase "fuzz/type/top-tuple" #[.tuple #[]], rng1)
  else if shape = 13 then
    let (c, rng2) := genOrdinaryCell rng1
    let (badTop, rng3) := pickNonCellTop rng2
    (mkXctosCase "fuzz/type/deep-top-not-cell" #[.cell c, badTop], rng3)
  else if shape = 14 then
    (mkXctosCase "fuzz/gas/exact"
      #[.cell cOrdRefs1]
      #[.pushInt (.num xctosSetGasExact), .tonEnvOp .setGasLimit, xctosInstr], rng1)
  else if shape = 15 then
    (mkXctosCase "fuzz/gas/exact-minus-one"
      #[.cell cOrdRefs1]
      #[.pushInt (.num xctosSetGasExactMinusOne), .tonEnvOp .setGasLimit, xctosInstr], rng1)
  else if shape = 16 then
    let (c, rng2) := genOrdinaryCell rng1
    (mkXctosCase s!"fuzz/ok/top/ordinary-boundary/bits-{c.bits.size}/refs-{c.refs.size}" #[.cell c], rng2)
  else
    let (c, rng2) := pickSpecialCell rng1
    (mkXctosCase "fuzz/ok/deep/special-two-below" #[.null, intV 4, .cell c], rng2)

def suite : InstrSuite where
  id := xctosId
  unit := #[
    { name := "unit/direct/success-ordinary-and-special-flag"
      run := do
        let checks : Array (String × Cell) :=
          #[
            ("ordinary-empty", cOrdEmpty),
            ("ordinary-bits7", cOrdBits7),
            ("ordinary-bits255", cOrdBits255),
            ("ordinary-refs1", cOrdRefs1),
            ("ordinary-refs4", cOrdRefs4),
            ("ordinary-bits1023", cOrdBits1023),
            ("ordinary-nested", cOrdNested),
            ("special-library-a", specialLibraryCellA),
            ("special-library-b", specialLibraryCellB)
          ]
        for (tag, c) in checks do
          expectOkStack s!"ok/{tag}"
            (runXctosDirect #[.cell c])
            (expectedXctosStack #[] c)

        expectOkStack "ok/deep-preserve-below-ordinary"
          (runXctosDirect #[.null, intV 11, .cell cOrdRefs1])
          (expectedXctosStack #[.null, intV 11] cOrdRefs1)

        expectOkStack "ok/deep-preserve-below-special"
          (runXctosDirect #[.builder Builder.empty, .cell specialLibraryCellA])
          (expectedXctosStack #[.builder Builder.empty] specialLibraryCellA) }
    ,
    { name := "unit/direct/underflow-type-and-no-rangechk"
      run := do
        expectErr "underflow/empty" (runXctosDirect #[]) .stkUnd

        expectErr "type/top-null" (runXctosDirect #[.null]) .typeChk
        expectErr "type/top-int" (runXctosDirect #[intV 3]) .typeChk
        expectErr "type/top-slice" (runXctosDirect #[.slice (Slice.ofCell Cell.empty)]) .typeChk
        expectErr "type/top-builder" (runXctosDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple" (runXctosDirect #[.tuple #[]]) .typeChk
        expectErr "type/deep-top-not-cell-null" (runXctosDirect #[.cell cOrdBits7, .null]) .typeChk
        expectErr "type/deep-top-not-cell-slice"
          (runXctosDirect #[.cell cOrdBits7, .slice (Slice.ofCell Cell.empty)]) .typeChk

        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("ok-ordinary", runXctosDirect #[.cell cOrdEmpty]),
            ("ok-special", runXctosDirect #[.cell specialLibraryCellA]),
            ("underflow", runXctosDirect #[]),
            ("type", runXctosDirect #[.null])
          ]
        for (label, res) in probes do
          match res with
          | .error .rangeChk =>
              throw (IO.userError s!"{label}: unexpected rangeChk for XCTOS")
          | _ => pure () }
    ,
    { name := "unit/direct/cell-load-gas-cache-ordinary"
      run := do
        let c : Cell := cOrdRefs4
        let h : Array UInt8 := Cell.hashBytes c
        let expected : Array Value := expectedXctosStack #[] c

        let (resFresh, stFresh) := runXctosRaw #[.cell c]
        match resFresh with
        | .ok _ =>
            if stFresh.stack == expected then
              pure ()
            else
              throw (IO.userError s!"fresh/ordinary: expected stack {reprStr expected}, got {reprStr stFresh.stack}")
            if stFresh.loadedCells == #[h] then
              pure ()
            else
              throw (IO.userError s!"fresh/ordinary: expected loaded cache [hash], got {reprStr stFresh.loadedCells}")
            if stFresh.gas.gasConsumed = cellLoadGasPrice then
              pure ()
            else
              throw (IO.userError s!"fresh/ordinary: expected gas {cellLoadGasPrice}, got {stFresh.gas.gasConsumed}")
        | .error e =>
            throw (IO.userError s!"fresh/ordinary: expected success, got {e}")

        let (resReload, stReload) := runXctosRaw #[.cell c] #[h]
        match resReload with
        | .ok _ =>
            if stReload.stack == expected then
              pure ()
            else
              throw (IO.userError s!"reload/ordinary: expected stack {reprStr expected}, got {reprStr stReload.stack}")
            if stReload.loadedCells == #[h] then
              pure ()
            else
              throw (IO.userError s!"reload/ordinary: expected loaded cache unchanged, got {reprStr stReload.loadedCells}")
            if stReload.gas.gasConsumed = cellReloadGasPrice then
              pure ()
            else
              throw (IO.userError s!"reload/ordinary: expected gas {cellReloadGasPrice}, got {stReload.gas.gasConsumed}")
        | .error e =>
            throw (IO.userError s!"reload/ordinary: expected success, got {e}") }
    ,
    { name := "unit/direct/cell-load-gas-cache-special"
      run := do
        let c : Cell := specialLibraryCellA
        let h : Array UInt8 := Cell.hashBytes c
        let expected : Array Value := expectedXctosStack #[] c

        let (resFresh, stFresh) := runXctosRaw #[.cell c]
        match resFresh with
        | .ok _ =>
            if stFresh.stack == expected then
              pure ()
            else
              throw (IO.userError s!"fresh/special: expected stack {reprStr expected}, got {reprStr stFresh.stack}")
            if stFresh.loadedCells == #[h] then
              pure ()
            else
              throw (IO.userError s!"fresh/special: expected loaded cache [hash], got {reprStr stFresh.loadedCells}")
            if stFresh.gas.gasConsumed = cellLoadGasPrice then
              pure ()
            else
              throw (IO.userError s!"fresh/special: expected gas {cellLoadGasPrice}, got {stFresh.gas.gasConsumed}")
        | .error e =>
            throw (IO.userError s!"fresh/special: expected success, got {e}")

        let (resReload, stReload) := runXctosRaw #[.cell c] #[h]
        match resReload with
        | .ok _ =>
            if stReload.stack == expected then
              pure ()
            else
              throw (IO.userError s!"reload/special: expected stack {reprStr expected}, got {reprStr stReload.stack}")
            if stReload.loadedCells == #[h] then
              pure ()
            else
              throw (IO.userError s!"reload/special: expected loaded cache unchanged, got {reprStr stReload.loadedCells}")
            if stReload.gas.gasConsumed = cellReloadGasPrice then
              pure ()
            else
              throw (IO.userError s!"reload/special: expected gas {cellReloadGasPrice}, got {stReload.gas.gasConsumed}")
        | .error e =>
            throw (IO.userError s!"reload/special: expected success, got {e}") }
    ,
    { name := "unit/opcode-decode-boundaries"
      run := do
        let xctosOnly ←
          match assembleCp0 [xctosInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/xctos failed: {e}")
        if xctosOnly.bits == natToBits xctosOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/xctos: expected 0xd739, got bits {xctosOnly.bits}")
        if xctosOnly.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/xctos: expected 16 bits, got {xctosOnly.bits.size}")

        let ctosOnly ←
          match assembleCp0 [ctosInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/ctos failed: {e}")
        if ctosOnly.bits == natToBits ctosOpcode 8 then
          pure ()
        else
          throw (IO.userError s!"assemble/ctos: expected 0xd0, got bits {ctosOnly.bits}")

        let program : Array Instr := #[splitInstr, splitQInstr, xctosInstr, .ldref, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/decode-seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/split-d736" s0 splitInstr 16
        let s2 ← expectDecodeStep "decode/splitq-d737" s1 splitQInstr 16
        let s3 ← expectDecodeStep "decode/xctos-d739" s2 xctosInstr 16
        let s4 ← expectDecodeStep "decode/ldref-d4" s3 .ldref 8
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let raw := mkSliceFromBits
          (natToBits 0xd737 16 ++ natToBits 0xd739 16 ++
            natToBits 0xd73a 16 ++ natToBits 0xd73b 16 ++ addCell.bits)
        let r1 ← expectDecodeStep "decode/raw-splitq-d737" raw splitQInstr 16
        let r2 ← expectDecodeStep "decode/raw-xctos-d739" r1 xctosInstr 16
        let r3 ← expectDecodeStep "decode/raw-xload-d73a" r2 xloadInstr 16
        let r4 ← expectDecodeStep "decode/raw-xloadq-d73b" r3 xloadQInstr 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining")

        expectDecodeErr "decode/raw-gap-0xd738"
          (mkSliceFromBits (natToBits 0xd738 16))
          .invOpcode }
    ,
    { name := "unit/dispatch/non-xctos-falls-through"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runXctosDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/fallback-ctos"
          (runXctosDispatchFallback ctosInstr #[.cell cOrdEmpty])
          #[.cell cOrdEmpty, intV dispatchSentinel]
        expectOkStack "dispatch/fallback-splitq"
          (runXctosDispatchFallback splitQInstr #[intV 5])
          #[intV 5, intV dispatchSentinel] }
  ]
  oracle := #[
    mkXctosCase "ok/ordinary-empty" #[.cell cOrdEmpty],
    mkXctosCase "ok/ordinary-bits7" #[.cell cOrdBits7],
    mkXctosCase "ok/ordinary-bits255" #[.cell cOrdBits255],
    mkXctosCase "ok/ordinary-refs1" #[.cell cOrdRefs1],
    mkXctosCase "ok/ordinary-refs4" #[.cell cOrdRefs4],
    mkXctosCase "ok/ordinary-bits1023" #[.cell cOrdBits1023],
    mkXctosCase "ok/ordinary-nested" #[.cell cOrdNested],
    mkXctosCase "ok/ordinary-mixed-bits-refs"
      #[.cell (Cell.mkOrdinary (stripeBits 41 3) #[refLeafA, refLeafD])],

    mkXctosCase "ok/special-library-a" #[.cell specialLibraryCellA],
    mkXctosCase "ok/special-library-b" #[.cell specialLibraryCellB],

    mkXctosCase "ok/deep-preserve-null-ordinary" #[.null, .cell cOrdBits7],
    mkXctosCase "ok/deep-preserve-int-special" #[intV (-15), .cell specialLibraryCellA],
    mkXctosCase "ok/deep-preserve-cell-ordinary" #[.cell refLeafA, .cell cOrdRefs4],
    mkXctosCase "ok/deep-preserve-builder-special" #[.builder Builder.empty, .cell specialLibraryCellB],
    mkXctosCase "ok/deep-preserve-two-values-ordinary" #[.null, intV 5, .cell cOrdBits255],

    mkXctosCase "underflow/empty" #[],
    mkXctosCase "type/top-null" #[.null],
    mkXctosCase "type/top-int" #[intV 42],
    mkXctosCase "type/top-slice" #[.slice (Slice.ofCell Cell.empty)],
    mkXctosCase "type/top-builder" #[.builder Builder.empty],
    mkXctosCase "type/top-tuple" #[.tuple #[]],
    mkXctosCase "type/deep-top-not-cell-null" #[.cell cOrdBits7, .null],
    mkXctosCase "type/deep-top-not-cell-slice" #[.cell cOrdBits7, .slice (Slice.ofCell Cell.empty)],

    mkXctosCase "gas/exact-cost-succeeds"
      #[.cell cOrdRefs1]
      #[.pushInt (.num xctosSetGasExact), .tonEnvOp .setGasLimit, xctosInstr],
    mkXctosCase "gas/exact-minus-one-out-of-gas"
      #[.cell cOrdRefs1]
      #[.pushInt (.num xctosSetGasExactMinusOne), .tonEnvOp .setGasLimit, xctosInstr]
  ]
  fuzz := #[
    { seed := 2026021017
      count := 500
      gen := genXctosFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.XCTOS
