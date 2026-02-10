import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.CTOS

/-
CTOS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ctos.lean` (`.ctos`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.ctos` encodes to `0xd0`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd0` decodes to `.ctos`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_cell_to_slice`, opcode `0xd0`)
  - `/Users/daniil/Coding/ton/crypto/vm/cells/CellSlice.cpp`
    (`load_cell_slice_impl`: register cell load before special-cell rejection).

Branch map covered by this suite:
- dispatch guard (`.ctos` vs fallback `next`);
- top pop via `VM.popCell` (`stkUnd` / `typeChk` / success);
- cell-load accounting branch (`cellLoadGasPrice` for first load, `cellReloadGasPrice` if cached);
- special-cell split after load accounting (`cellUnd` for special, success for ordinary);
- opcode/decode boundaries around `0xd0` (CTOS) and neighbors (`0xce`, `0xd1`, `0xd739`, `0xd4`).
-/

private def ctosId : InstrId := { name := "CTOS" }

private def ctosInstr : Instr := .ctos

private def xctosInstr : Instr := .xctos

private def ctosOpcode : Nat := 0xd0

private def xctosOpcode : Nat := 0xd739

private def dispatchSentinel : Int := 537

private def mkCtosCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ctosInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ctosId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runCtosDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellCtos ctosInstr stack

private def runCtosDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellCtos instr (VM.push (intV dispatchSentinel)) stack

private def runCtosRaw
    (stack : Array Value)
    (loadedCells : Array (Array UInt8) := #[]) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, loadedCells := loadedCells }
  let (res, st1) := (execInstrCellCtos ctosInstr (pure ())).run st0
  (res, st1)

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

private def ctosSetGasExact : Int :=
  -- CTOS uses `registerCellLoad`: add explicit cell-load price to the fixed-point budget.
  computeExactGasBudgetWithExtra ctosInstr cellLoadGasPrice

private def ctosSetGasExactMinusOne : Int :=
  if ctosSetGasExact > 0 then ctosSetGasExact - 1 else 0

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun i => ((i.1 + phase) % 2 = 1)

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

private def specialLibraryCell : Cell :=
  -- Type byte `2` (library), then 256-bit hash payload.
  { bits := natToBits 2 8 ++ Array.replicate 256 false
    refs := #[]
    special := true
    levelMask := 0 }

private def expectedCtosStack (below : Array Value) (c : Cell) : Array Value :=
  below ++ #[.slice (Slice.ofCell c)]

private def ctosBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 63, 64, 127, 255, 256, 511, 1023]

private def pickBitsLenBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (ctosBitsBoundaryPool.size - 1)
  (ctosBitsBoundaryPool[idx]!, rng')

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

private def genCtosFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    (mkCtosCase "fuzz/ok/top-empty" #[.cell cOrdEmpty], rng1)
  else if shape = 1 then
    let (c, rng2) := genOrdinaryCell rng1
    (mkCtosCase s!"fuzz/ok/top/bits-{c.bits.size}/refs-{c.refs.size}" #[.cell c], rng2)
  else if shape = 2 then
    let (c, rng2) := genOrdinaryCell rng1
    let (noise, rng3) := pickNoise rng2
    (mkCtosCase s!"fuzz/ok/deep/bits-{c.bits.size}/refs-{c.refs.size}" #[noise, .cell c], rng3)
  else if shape = 3 then
    (mkCtosCase "fuzz/ok/top-max-1023" #[.cell cOrdBits1023], rng1)
  else if shape = 4 then
    (mkCtosCase "fuzz/ok/top-refs4" #[.cell cOrdRefs4], rng1)
  else if shape = 5 then
    (mkCtosCase "fuzz/special/top-cellund" #[.cell specialLibraryCell], rng1)
  else if shape = 6 then
    (mkCtosCase "fuzz/special/deep-cellund" #[intV 7, .cell specialLibraryCell], rng1)
  else if shape = 7 then
    (mkCtosCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 8 then
    (mkCtosCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 9 then
    (mkCtosCase "fuzz/type/top-int" #[intV 0], rng1)
  else if shape = 10 then
    (mkCtosCase "fuzz/type/top-slice" #[.slice (Slice.ofCell Cell.empty)], rng1)
  else if shape = 11 then
    (mkCtosCase "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
  else if shape = 12 then
    let (c, rng2) := genOrdinaryCell rng1
    let (badTop, rng3) := pickNonCellTop rng2
    (mkCtosCase "fuzz/type/deep-top-not-cell" #[.cell c, badTop], rng3)
  else if shape = 13 then
    (mkCtosCase "fuzz/gas/exact"
      #[.cell cOrdRefs1]
      #[.pushInt (.num ctosSetGasExact), .tonEnvOp .setGasLimit, ctosInstr], rng1)
  else if shape = 14 then
    (mkCtosCase "fuzz/gas/exact-minus-one"
      #[.cell cOrdRefs1]
      #[.pushInt (.num ctosSetGasExactMinusOne), .tonEnvOp .setGasLimit, ctosInstr], rng1)
  else
    let (c, rng2) := genOrdinaryCell rng1
    (mkCtosCase s!"fuzz/ok/top-boundary/bits-{c.bits.size}/refs-{c.refs.size}" #[.cell c], rng2)

def suite : InstrSuite where
  id := ctosId
  unit := #[
    { name := "unit/direct/success-converts-cell-to-full-slice"
      run := do
        let checks : Array (String × Cell) :=
          #[
            ("empty", cOrdEmpty),
            ("bits7", cOrdBits7),
            ("bits255", cOrdBits255),
            ("refs1", cOrdRefs1),
            ("refs4", cOrdRefs4),
            ("bits1023", cOrdBits1023),
            ("nested", cOrdNested)
          ]
        for (tag, c) in checks do
          expectOkStack s!"ok/{tag}"
            (runCtosDirect #[.cell c])
            (expectedCtosStack #[] c)

        expectOkStack "ok/deep-stack-preserve-below"
          (runCtosDirect #[.null, intV 11, .cell cOrdRefs1])
          (expectedCtosStack #[.null, intV 11] cOrdRefs1) }
    ,
    { name := "unit/direct/underflow-type-and-no-rangechk"
      run := do
        expectErr "underflow/empty" (runCtosDirect #[]) .stkUnd

        expectErr "type/top-null" (runCtosDirect #[.null]) .typeChk
        expectErr "type/top-int" (runCtosDirect #[intV 3]) .typeChk
        expectErr "type/top-slice" (runCtosDirect #[.slice (Slice.ofCell Cell.empty)]) .typeChk
        expectErr "type/top-builder" (runCtosDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple" (runCtosDirect #[.tuple #[]]) .typeChk
        expectErr "type/deep-top-not-cell-null" (runCtosDirect #[.cell cOrdBits7, .null]) .typeChk
        expectErr "type/deep-top-not-cell-slice"
          (runCtosDirect #[.cell cOrdBits7, .slice (Slice.ofCell Cell.empty)]) .typeChk

        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("ok", runCtosDirect #[.cell cOrdEmpty]),
            ("underflow", runCtosDirect #[]),
            ("type", runCtosDirect #[.null]),
            ("special", runCtosDirect #[.cell specialLibraryCell])
          ]
        for (label, res) in probes do
          match res with
          | .error .rangeChk =>
              throw (IO.userError s!"{label}: unexpected rangeChk for CTOS")
          | _ => pure () }
    ,
    { name := "unit/direct/special-cellund-after-pop"
      run := do
        let (res0, st0) := runCtosRaw #[.cell specialLibraryCell]
        match res0 with
        | .error .cellUnd =>
            if st0.stack == #[] then
              pure ()
            else
              throw (IO.userError s!"special/no-below: expected empty stack, got {reprStr st0.stack}")
        | .error e =>
            throw (IO.userError s!"special/no-below: expected cellUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "special/no-below: expected cellUnd, got success")

        let (res1, st1) := runCtosRaw #[intV 7, .cell specialLibraryCell]
        match res1 with
        | .error .cellUnd =>
            let expected : Array Value := #[intV 7]
            if st1.stack == expected then
              pure ()
            else
              throw (IO.userError s!"special/with-below: expected stack {reprStr expected}, got {reprStr st1.stack}")
        | .error e =>
            throw (IO.userError s!"special/with-below: expected cellUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "special/with-below: expected cellUnd, got success") }
    ,
    { name := "unit/direct/cell-load-gas-cache-success"
      run := do
        let c : Cell := cOrdRefs4
        let h : Array UInt8 := Cell.hashBytes c
        let expected : Array Value := expectedCtosStack #[] c

        let (resFresh, stFresh) := runCtosRaw #[.cell c]
        match resFresh with
        | .ok _ =>
            if stFresh.stack == expected then
              pure ()
            else
              throw (IO.userError s!"fresh/success: expected stack {reprStr expected}, got {reprStr stFresh.stack}")
            if stFresh.loadedCells == #[h] then
              pure ()
            else
              throw (IO.userError s!"fresh/success: expected loaded cache [hash], got {reprStr stFresh.loadedCells}")
            if stFresh.gas.gasConsumed = cellLoadGasPrice then
              pure ()
            else
              throw (IO.userError s!"fresh/success: expected gas {cellLoadGasPrice}, got {stFresh.gas.gasConsumed}")
        | .error e =>
            throw (IO.userError s!"fresh/success: expected success, got {e}")

        let (resReload, stReload) := runCtosRaw #[.cell c] #[h]
        match resReload with
        | .ok _ =>
            if stReload.stack == expected then
              pure ()
            else
              throw (IO.userError s!"reload/success: expected stack {reprStr expected}, got {reprStr stReload.stack}")
            if stReload.loadedCells == #[h] then
              pure ()
            else
              throw (IO.userError s!"reload/success: expected loaded cache unchanged, got {reprStr stReload.loadedCells}")
            if stReload.gas.gasConsumed = cellReloadGasPrice then
              pure ()
            else
              throw (IO.userError s!"reload/success: expected gas {cellReloadGasPrice}, got {stReload.gas.gasConsumed}")
        | .error e =>
            throw (IO.userError s!"reload/success: expected success, got {e}") }
    ,
    { name := "unit/direct/cell-load-gas-cache-special-reject"
      run := do
        let h : Array UInt8 := Cell.hashBytes specialLibraryCell

        let (resFresh, stFresh) := runCtosRaw #[.cell specialLibraryCell]
        match resFresh with
        | .error .cellUnd =>
            if stFresh.stack == #[] then
              pure ()
            else
              throw (IO.userError s!"fresh/special: expected empty stack, got {reprStr stFresh.stack}")
            if stFresh.loadedCells == #[h] then
              pure ()
            else
              throw (IO.userError s!"fresh/special: expected loaded cache [hash], got {reprStr stFresh.loadedCells}")
            if stFresh.gas.gasConsumed = cellLoadGasPrice then
              pure ()
            else
              throw (IO.userError s!"fresh/special: expected gas {cellLoadGasPrice}, got {stFresh.gas.gasConsumed}")
        | .error e =>
            throw (IO.userError s!"fresh/special: expected cellUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "fresh/special: expected cellUnd, got success")

        let (resReload, stReload) := runCtosRaw #[.cell specialLibraryCell] #[h]
        match resReload with
        | .error .cellUnd =>
            if stReload.stack == #[] then
              pure ()
            else
              throw (IO.userError s!"reload/special: expected empty stack, got {reprStr stReload.stack}")
            if stReload.loadedCells == #[h] then
              pure ()
            else
              throw (IO.userError s!"reload/special: expected loaded cache unchanged, got {reprStr stReload.loadedCells}")
            if stReload.gas.gasConsumed = cellReloadGasPrice then
              pure ()
            else
              throw (IO.userError s!"reload/special: expected gas {cellReloadGasPrice}, got {stReload.gas.gasConsumed}")
        | .error e =>
            throw (IO.userError s!"reload/special: expected cellUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "reload/special: expected cellUnd, got success") }
    ,
    { name := "unit/opcode-decode-boundaries-and-dispatch"
      run := do
        let ctosOnly ←
          match assembleCp0 [ctosInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/ctos failed: {e}")
        if ctosOnly.bits == natToBits ctosOpcode 8 then
          pure ()
        else
          throw (IO.userError s!"assemble/ctos: expected 0xd0, got bits {ctosOnly.bits}")
        if ctosOnly.bits.size = 8 then
          pure ()
        else
          throw (IO.userError s!"assemble/ctos: expected 8 bits, got {ctosOnly.bits.size}")

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

        let program : Array Instr := #[.stSlice false false, ctosInstr, .ends, xctosInstr, .ldref, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/decode-seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stslice-ce" s0 (.stSlice false false) 8
        let s2 ← expectDecodeStep "decode/ctos-d0" s1 ctosInstr 8
        let s3 ← expectDecodeStep "decode/ends-d1" s2 .ends 8
        let s4 ← expectDecodeStep "decode/xctos-d739" s3 xctosInstr 16
        let s5 ← expectDecodeStep "decode/ldref-d4" s4 .ldref 8
        let s6 ← expectDecodeStep "decode/tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        expectOkStack "dispatch/fallback"
          (runCtosDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel] }
  ]
  oracle := #[
    mkCtosCase "ok/ordinary-empty" #[.cell cOrdEmpty],
    mkCtosCase "ok/ordinary-bits7" #[.cell cOrdBits7],
    mkCtosCase "ok/ordinary-bits255" #[.cell cOrdBits255],
    mkCtosCase "ok/ordinary-refs1" #[.cell cOrdRefs1],
    mkCtosCase "ok/ordinary-refs4" #[.cell cOrdRefs4],
    mkCtosCase "ok/ordinary-bits1023" #[.cell cOrdBits1023],
    mkCtosCase "ok/ordinary-nested" #[.cell cOrdNested],
    mkCtosCase "ok/deep-preserve-null" #[.null, .cell cOrdBits7],
    mkCtosCase "ok/deep-preserve-int" #[intV (-15), .cell cOrdRefs1],
    mkCtosCase "ok/deep-preserve-cell" #[.cell refLeafA, .cell cOrdRefs4],
    mkCtosCase "ok/deep-preserve-builder" #[.builder Builder.empty, .cell cOrdNested],
    mkCtosCase "ok/deep-preserve-two-values" #[.null, intV 5, .cell cOrdBits255],

    mkCtosCase "special/top-cellund" #[.cell specialLibraryCell],
    mkCtosCase "special/deep-cellund" #[intV 9, .cell specialLibraryCell],

    mkCtosCase "underflow/empty" #[],
    mkCtosCase "type/top-null" #[.null],
    mkCtosCase "type/top-int" #[intV 42],
    mkCtosCase "type/top-slice" #[.slice (Slice.ofCell Cell.empty)],
    mkCtosCase "type/top-builder" #[.builder Builder.empty],
    mkCtosCase "type/top-tuple" #[.tuple #[]],
    mkCtosCase "type/deep-top-not-cell-null" #[.cell cOrdBits7, .null],
    mkCtosCase "type/deep-top-not-cell-slice" #[.cell cOrdBits7, .slice (Slice.ofCell Cell.empty)],

    mkCtosCase "gas/exact-cost-succeeds"
      #[.cell cOrdRefs1]
      #[.pushInt (.num ctosSetGasExact), .tonEnvOp .setGasLimit, ctosInstr],
    mkCtosCase "gas/exact-minus-one-out-of-gas"
      #[.cell cOrdRefs1]
      #[.pushInt (.num ctosSetGasExactMinusOne), .tonEnvOp .setGasLimit, ctosInstr]
  ]
  fuzz := #[
    { seed := 2026021016
      count := 320
      gen := genCtosFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.CTOS
