import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.LDDICTQ

/-!
INSTRUCTION: LDDICTQ

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime dispatch.
   - `execInstrDictLddict` handles `.lddict preload quiet`; all others continue to `next`.

2. [B2] Stack arity check (`popSlice`).
   - One stack item required; empty stack throws `.stkUnd`.

3. [B3] First-bit availability gate (`s.haveBits 1`).
   - If true: proceed to `present := s.readBits 1`.
   - If false: no dict value can be read and execution routes to the `!ok` path.

4. [B4] Ref availability for present branch (`s.haveRefs needRefs`).
   - When first bit is 1, `needRefs = 1`; missing refs cause `ok = false` and error/noise behavior below.

5. [B5] Non-quiet failure path.
   - `ok = false`, `quiet = false` → throw `.cellUnd`.

6. [B6] Quiet failure-noise branch.
   - `ok = false`, `quiet = true`.
   - If `preload = true`, only `0` is pushed.
   - If `preload = false`, original slice and `0` are pushed.

7. [B7] Present success branch (`present = true`).
   - `needRefs = 1`, pushes referenced cell.
   - `preload = false` pushes advanced slice (bitPos + 1, refPos + 1).
   - `preload = true` does not push source slice.

8. [B8] Miss success branch (`present = false`).
   - Pushes `.null`.
   - `preload = false` pushes advanced slice (bitPos + 1).
   - `preload = true` does not push source slice.

9. [B9] Quiet success marker.
   - `quiet = true` always pushes `-1` after success value path.

10. [B10] Assembler validation and encoding.
   - `.lddict false false` → `0xf404`
   - `.lddict true false`  → `0xf405`
   - `.lddict false true`  → `0xf406`
   - `.lddict true true`   → `0xf407`
   - There are no unsupported bit combinations for this constructor family in the assembler.

11. [B11] Decoder boundaries and adjacency.
   - `0xf404..0xf407` decode to `.lddict preload quiet` with `{preload,quiet}` from low bits.
   - Adjacent opcodes (e.g. `0xf408`, `0xf409`) are invalid and decode to `.invOpcode`.
   - Truncated `0xf4` (8-bit) is invalid.

12. [B12] Gas accounting.
   - Base cost appears fixed for this family in the model/refs; exact and exact-minus-one gas behaviors should be checked.

TOTAL BRANCHES: 12

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is expected to be covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "LDDICTQ" }

private def lddictNP : Instr := .lddict false false
private def lddictP : Instr := .lddict true false
private def lddictNQ : Instr := .lddict false true
private def lddictPQ : Instr := .lddict true true

private def loadValueA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def loadValueB : Cell := Cell.mkOrdinary (natToBits 0xB2 16) #[]
private def loadValueC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]
private def loadValueD : Cell := Cell.mkOrdinary (natToBits 0xD4 8) #[]

private def presentSliceMin : Slice := mkSliceWithBitsRefs #[true] #[loadValueA]
private def presentSliceA : Slice := mkSliceWithBitsRefs (natToBits 0b1011_0010 8) #[loadValueA]
private def presentSliceB : Slice := mkSliceWithBitsRefs (natToBits 0b1001_1101 8) #[loadValueA, loadValueB, loadValueC]
private def presentSliceC : Slice := mkSliceWithBitsRefs (natToBits 0b1101_0110 8) #[loadValueB]
private def presentSliceTail1 : Slice := mkSliceWithBitsRefs (natToBits 0b1110_1100 8) #[loadValueD]
private def presentSliceNoRef : Slice := mkSliceFromBits #[true]

private def missSliceA : Slice := mkSliceWithBitsRefs #[false] #[]
private def missSliceB : Slice := mkSliceWithBitsRefs (natToBits 0b0110_1001 8) #[]
private def missSliceC : Slice := mkSliceWithBitsRefs (natToBits 0b0000_1111 8) #[]
private def missSliceTail1 : Slice := mkSliceWithBitsRefs (natToBits 0b0110_0011 8) #[]
private def missSliceNoBits : Slice := mkSliceFromBits #[]

private def opcodeF404 : Nat := 0xf404
private def opcodeF405 : Nat := 0xf405
private def opcodeF406 : Nat := 0xf406
private def opcodeF407 : Nat := 0xf407
private def opcodeF408 : Nat := 0xf408
private def opcodeF409 : Nat := 0xf409

private def rawF404 : Cell := Cell.mkOrdinary (natToBits opcodeF404 16) #[]
private def rawF405 : Cell := Cell.mkOrdinary (natToBits opcodeF405 16) #[]
private def rawF406 : Cell := Cell.mkOrdinary (natToBits opcodeF406 16) #[]
private def rawF407 : Cell := Cell.mkOrdinary (natToBits opcodeF407 16) #[]
private def rawF408 : Cell := Cell.mkOrdinary (natToBits opcodeF408 16) #[]
private def rawF409 : Cell := Cell.mkOrdinary (natToBits opcodeF409 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def opcodeSlice16 (w : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits w 16) #[])

private def runLddictDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictLddict instr stack

private def runLddictDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictLddict instr (VM.push (intV 42_001)) stack

private def expectDecodeInvOpcode (label : String) (w : Nat) : IO Unit := do
  match decodeCp0WithBits (opcodeSlice16 w) with
  | .error .invOpcode => pure ()
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got instr={reprStr instr}, bits={bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lddictNP])
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

private def advanceBit1 (s : Slice) : Slice :=
  { s with bitPos := s.bitPos + 1, refPos := s.refPos + 1 }

private def advanceBit0 (s : Slice) : Slice :=
  { s with bitPos := s.bitPos + 1, refPos := s.refPos }

private def lddictGasNP : Int := computeExactGasBudget lddictNP
private def lddictGasP : Int := computeExactGasBudget lddictP
private def lddictGasNQ : Int := computeExactGasBudget lddictNQ
private def lddictGasPQ : Int := computeExactGasBudget lddictPQ

private def lddictGasMinusOneNP : Int := computeExactGasBudgetMinusOne lddictNP
private def lddictGasMinusOneP : Int := computeExactGasBudgetMinusOne lddictP
private def lddictGasMinusOneNQ : Int := computeExactGasBudgetMinusOne lddictNQ
private def lddictGasMinusOnePQ : Int := computeExactGasBudgetMinusOne lddictPQ

private def genLddictqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let shapePair := randNat rng0 0 34
  let shape := shapePair.1
  let rng1 := shapePair.2
  let noisePrefixPair : Array Value × StdGen :=
    match randNat rng1 0 5 with
    | (0, r) => (#[], r)
    | (1, r) => (#[intV 7], r)
    | (2, r) => (#[intV 11, .cell loadValueC], r)
    | (3, r) => (#[intV (-2), .slice missSliceC], r)
    | (4, r) => (#[intV 100, .null], r)
    | (_, r) => (#[intV 3, .slice presentSliceTail1], r)
  let noisePrefix : Array Value := noisePrefixPair.1
  let rng2 : StdGen := noisePrefixPair.2
  let addNoisePrefix : Value → Array Value := fun v => noisePrefix.push v
  let baseName := s!"fuzz/{shape}"
  let case0 :=
    if shape = 0 then
      mkCase (s!"{baseName}/present/preload-false/quiet-false") (addNoisePrefix <| .slice presentSliceA) #[lddictNP]
    else if shape = 1 then
      mkCase (s!"{baseName}/present/preload-true/quiet-false") (addNoisePrefix <| .slice presentSliceB) #[lddictP]
    else if shape = 2 then
      mkCase (s!"{baseName}/present/preload-false/quiet-true") (addNoisePrefix <| .slice presentSliceC) #[lddictNQ]
    else if shape = 3 then
      mkCase (s!"{baseName}/present/preload-true/quiet-true") (addNoisePrefix <| .slice presentSliceTail1) #[lddictPQ]
    else if shape = 4 then
      mkCase (s!"{baseName}/miss/preload-false/quiet-false") (addNoisePrefix <| .slice missSliceA) #[lddictNP]
    else if shape = 5 then
      mkCase (s!"{baseName}/miss/preload-true/quiet-false") (addNoisePrefix <| .slice missSliceB) #[lddictP]
    else if shape = 6 then
      mkCase (s!"{baseName}/miss/preload-false/quiet-true") (addNoisePrefix <| .slice missSliceC) #[lddictNQ]
    else if shape = 7 then
      mkCase (s!"{baseName}/miss/preload-true/quiet-true") (addNoisePrefix <| .slice missSliceTail1) #[lddictPQ]
    else if shape = 8 then
      mkCase (s!"{baseName}/err/no-bits/quiet-false") (addNoisePrefix <| .slice missSliceNoBits) #[lddictNP]
    else if shape = 9 then
      mkCase (s!"{baseName}/err/no-bits/quiet-true") (addNoisePrefix <| .slice missSliceNoBits) #[lddictNQ]
    else if shape = 10 then
      mkCase (s!"{baseName}/err/missing-ref/quiet-false/preload-false") (addNoisePrefix <| .slice presentSliceNoRef) #[lddictNP]
    else if shape = 11 then
      mkCase (s!"{baseName}/err/missing-ref/quiet-false/preload-true") (addNoisePrefix <| .slice presentSliceNoRef) #[lddictP]
    else if shape = 12 then
      mkCase (s!"{baseName}/ok/missing-ref/quiet-true/preload-false") (addNoisePrefix <| .slice presentSliceNoRef) #[lddictNQ]
    else if shape = 13 then
      mkCase (s!"{baseName}/ok/missing-ref/quiet-true/preload-true") (addNoisePrefix <| .slice presentSliceNoRef) #[lddictPQ]
    else if shape = 14 then
      mkCaseCode (s!"{baseName}/decode/f404") (#[]) rawF404
    else if shape = 15 then
      mkCaseCode (s!"{baseName}/decode/f405") (#[]) rawF405
    else if shape = 16 then
      mkCaseCode (s!"{baseName}/decode/f406") (#[]) rawF406
    else if shape = 17 then
      mkCaseCode (s!"{baseName}/decode/f407") (#[]) rawF407
    else if shape = 18 then
      mkCaseCode (s!"{baseName}/decode/f408") (#[]) rawF408
    else if shape = 19 then
      mkCaseCode (s!"{baseName}/decode/f409") (#[]) rawF409
    else if shape = 20 then
      mkCaseCode (s!"{baseName}/decode/f4-truncated") (#[]) rawF4
    else if shape = 21 then
      mkCase (s!"{baseName}/gas/exact/np")
        (#[.slice presentSliceA])
        #[.pushInt (.num lddictGasNP), .tonEnvOp .setGasLimit, lddictNP]
        (oracleGasLimitsExact lddictGasNP)
    else if shape = 22 then
      mkCase (s!"{baseName}/gas/exact/p")
        (#[.slice presentSliceA])
        #[.pushInt (.num lddictGasP), .tonEnvOp .setGasLimit, lddictP]
        (oracleGasLimitsExact lddictGasP)
    else if shape = 23 then
      mkCase (s!"{baseName}/gas/exact/nq")
        (#[.slice presentSliceA])
        #[.pushInt (.num lddictGasNQ), .tonEnvOp .setGasLimit, lddictNQ]
        (oracleGasLimitsExact lddictGasNQ)
    else if shape = 24 then
      mkCase (s!"{baseName}/gas/exact/pq")
        (#[.slice presentSliceA])
        #[.pushInt (.num lddictGasPQ), .tonEnvOp .setGasLimit, lddictPQ]
        (oracleGasLimitsExact lddictGasPQ)
    else if shape = 25 then
      mkCase (s!"{baseName}/gas/exact-minus-one/np")
        (#[.slice presentSliceA])
        #[.pushInt (.num lddictGasMinusOneNP), .tonEnvOp .setGasLimit, lddictNP]
        (oracleGasLimitsExactMinusOne lddictGasMinusOneNP)
    else if shape = 26 then
      mkCase (s!"{baseName}/gas/exact-minus-one/p")
        (#[.slice presentSliceA])
        #[.pushInt (.num lddictGasMinusOneP), .tonEnvOp .setGasLimit, lddictP]
        (oracleGasLimitsExactMinusOne lddictGasMinusOneP)
    else if shape = 27 then
      mkCase (s!"{baseName}/gas/exact-minus-one/nq")
        (#[.slice presentSliceA])
        #[.pushInt (.num lddictGasMinusOneNQ), .tonEnvOp .setGasLimit, lddictNQ]
        (oracleGasLimitsExactMinusOne lddictGasMinusOneNQ)
    else if shape = 28 then
      mkCase (s!"{baseName}/gas/exact-minus-one/pq")
        (#[.slice presentSliceA])
        #[.pushInt (.num lddictGasMinusOnePQ), .tonEnvOp .setGasLimit, lddictPQ]
        (oracleGasLimitsExactMinusOne lddictGasMinusOnePQ)
    else if shape = 29 then
      mkCase (s!"{baseName}/prefix-noise/success") (#[intV 7, .cell loadValueA, .slice presentSliceB]) #[lddictNP]
    else if shape = 30 then
      mkCase (s!"{baseName}/prefix-noise/miss") (#[intV 7, .cell loadValueB, .slice missSliceB]) #[lddictNQ]
    else if shape = 31 then
      mkCase (s!"{baseName}/type-error/top-null") (addNoisePrefix .null) #[lddictNP]
    else if shape = 32 then
      mkCase (s!"{baseName}/type-error/top-builder") (addNoisePrefix (.builder Builder.empty)) #[lddictNP]
    else if shape = 33 then
      mkCase (s!"{baseName}/type-error/top-cont") (addNoisePrefix (.cont (.quit 0))) #[lddictP]
    else
      let caseShape :=
        if shape % 2 = 0 then
          mkCase (s!"{baseName}/boundary/miss/noise") (#[.slice presentSliceA, intV 17]) #[lddictP]
        else
          mkCase (s!"{baseName}/boundary/present/noise") (#[.slice missSliceC, intV 17]) #[lddictNP]
      { caseShape with initStack := caseShape.initStack.push (if shape % 2 = 0 then .cell loadValueD else .cell loadValueC) }
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        let stack := #[.slice presentSliceA]
        expectOkStack "fallback" (runLddictDispatchFallback .add stack) #[.slice presentSliceA, intV 42_001]
        expectOkStack "match" (runLddictDirect lddictNP stack) #[.cell loadValueA, .slice (advanceBit1 presentSliceA)] },
    { name := "unit/stack/underflow-and-type"
      run := do
        expectErr "empty-stack" (runLddictDirect lddictNP #[]) .stkUnd
        expectErr "top-not-slice" (runLddictDirect lddictNP #[.int (.num 1)]) .typeChk },
    { name := "unit/present-success"
      run := do
        expectOkStack "present/preload-false/quiet-false"
          (runLddictDirect lddictNP #[.slice presentSliceB])
          (#[.cell loadValueA, .slice (advanceBit1 presentSliceB)])
        expectOkStack "present/preload-true/quiet-false"
          (runLddictDirect lddictP #[.slice presentSliceC])
          (#[.cell loadValueB])
        expectOkStack "present/preload-false/quiet-true"
          (runLddictDirect lddictNQ #[.slice presentSliceA])
          (#[.cell loadValueA, .slice (advanceBit1 presentSliceA), intV (-1)])
        expectOkStack "present/preload-true/quiet-true"
          (runLddictDirect lddictPQ #[.slice presentSliceTail1])
          (#[.cell loadValueD, intV (-1)]) },
    { name := "unit/miss-success"
      run := do
        expectOkStack "miss/preload-false/quiet-false"
          (runLddictDirect lddictNP #[.slice missSliceB])
          (#[.null, .slice (advanceBit0 missSliceB)])
        expectOkStack "miss/preload-true/quiet-false"
          (runLddictDirect lddictP #[.slice missSliceC])
          (#[.null])
        expectOkStack "miss/preload-false/quiet-true"
          (runLddictDirect lddictNQ #[.slice missSliceA])
          (#[.null, .slice (advanceBit0 missSliceA), intV (-1)])
        expectOkStack "miss/preload-true/quiet-true"
          (runLddictDirect lddictPQ #[.slice missSliceTail1])
          (#[.null, intV (-1)]) },
    { name := "unit/missing-refs-and-no-bits/quiet-cases"
      run := do
        expectErr "missing-refs/quiet-false/preload-false" (runLddictDirect lddictNP #[.slice presentSliceNoRef]) .cellUnd
        expectErr "missing-refs/quiet-false/preload-true" (runLddictDirect lddictP #[.slice presentSliceNoRef]) .cellUnd
        expectOkStack "missing-refs/quiet-true/preload-false"
          (runLddictDirect lddictNQ #[.slice presentSliceNoRef]) (#[.slice presentSliceNoRef, intV 0])
        expectOkStack "missing-refs/quiet-true/preload-true"
          (runLddictDirect lddictPQ #[.slice presentSliceNoRef]) (#[intV 0])
        expectErr "no-bits/quiet-false" (runLddictDirect lddictNP #[.slice missSliceNoBits]) .cellUnd
        expectOkStack "no-bits/quiet-true"
          (runLddictDirect lddictNQ #[.slice missSliceNoBits]) (#[.slice missSliceNoBits, intV 0]) },
    { name := "unit/stack-preservation"
      run := do
        expectOkStack "success/with-prefix"
          (runLddictDirect lddictNP #[intV 77, .cell loadValueA, .slice presentSliceB])
          #[intV 77, .cell loadValueA, .cell loadValueA, .slice (advanceBit1 presentSliceB)]
        expectOkStack "miss/with-prefix"
          (runLddictDirect lddictP #[intV 77, .cell loadValueB, .slice missSliceB])
          #[intV 77, .cell loadValueB, .null]
        expectOkStack "quiet-miss/with-prefix"
          (runLddictDirect lddictNQ #[intV 77, .tuple #[], .slice missSliceB])
          #[intV 77, .tuple #[], .null, .slice (advanceBit0 missSliceB), intV (-1)] },
    { name := "unit/assembler-encodings"
      run := do
        match assembleCp0 [lddictNP] with
        | .ok c =>
            if c.bits != natToBits opcodeF404 16 then
              throw (IO.userError s!"encode/f404 expected 0xf404, got {bitsToNat c.bits}")
        | .error e =>
            throw (IO.userError s!"encode/f404 expected success, got {e}")
        match assembleCp0 [lddictP] with
        | .ok c =>
            if c.bits != natToBits opcodeF405 16 then
              throw (IO.userError s!"encode/f405 expected 0xf405, got {bitsToNat c.bits}")
        | .error e =>
            throw (IO.userError s!"encode/f405 expected success, got {e}")
        match assembleCp0 [lddictNQ] with
        | .ok c =>
            if c.bits != natToBits opcodeF406 16 then
              throw (IO.userError s!"encode/f406 expected 0xf406, got {bitsToNat c.bits}")
        | .error e =>
            throw (IO.userError s!"encode/f406 expected success, got {e}")
        match assembleCp0 [lddictPQ] with
        | .ok c =>
            if c.bits != natToBits opcodeF407 16 then
              throw (IO.userError s!"encode/f407 expected 0xf407, got {bitsToNat c.bits}")
        | .error e =>
            throw (IO.userError s!"encode/f407 expected success, got {e}") },
    { name := "unit/decode-paths"
      run := do
        let _ ← expectDecodeStep "decode/f404" (opcodeSlice16 opcodeF404) lddictNP 16
        let _ ← expectDecodeStep "decode/f405" (opcodeSlice16 opcodeF405) lddictP 16
        let _ ← expectDecodeStep "decode/f406" (opcodeSlice16 opcodeF406) lddictNQ 16
        let _ ← expectDecodeStep "decode/f407" (opcodeSlice16 opcodeF407) lddictPQ 16
        expectDecodeInvOpcode "decode/f408" opcodeF408
        expectDecodeInvOpcode "decode/f409" opcodeF409
        match decodeCp0WithBits (Slice.ofCell rawF4) with
        | .error .invOpcode => pure ()
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode/f4-truncated: expected invOpcode, got instr={reprStr instr}, bits={bits}")
        | .error e =>
            throw (IO.userError s!"decode/f4-truncated: expected invOpcode, got {e}")
        let _ ← expectDecodeStep "decode/f403-lddicts-true" (opcodeSlice16 0xf403) (.dictExt (.lddicts true)) 16 },
    { name := "unit/decode-vs-adjacent-instructions"
      run := do
        match decodeCp0WithBits (opcodeSlice16 0xf402) with
        | .ok (instr, bits, _) =>
            if instr != .dictExt (.lddicts false) ∨ bits ≠ 16 then
              throw (IO.userError "decode/0xf402 mismatch expected lddicts false with 16 bits")
        | .error e =>
            throw (IO.userError s!"decode/0xf402 expected lddicts-false, got {e}") } ]
  oracle := #[
    mkCase "err/underflow-empty" #[], -- [B2]
    mkCase "err/top-not-slice" (#[intV 7]), -- [B2,B3]
    mkCase "err/no-bits-nonquiet" (#[.slice missSliceNoBits]) #[lddictNP], -- [B3,B4,B5]
    mkCase "ok/no-bits-quiet" (#[.slice missSliceNoBits]) #[lddictNQ], -- [B5,B6]
    mkCase "ok/present-nonquiet-preload-false" (#[.slice presentSliceA]) #[lddictNP], -- [B6,B7,B8]
    mkCase "ok/present-nonquiet-preload-true" (#[.slice presentSliceB]) #[lddictP], -- [B6,B7]
    mkCase "ok/present-quiet-preload-false" (#[.slice presentSliceC]) #[lddictNQ], -- [B7,B8,B9]
    mkCase "ok/present-quiet-preload-true" (#[.slice presentSliceTail1]) #[lddictPQ], -- [B7,B9]
    mkCase "ok/miss-nonquiet-preload-false" (#[.slice missSliceA]) #[lddictNP], -- [B3,B7,B8]
    mkCase "ok/miss-nonquiet-preload-true" (#[.slice missSliceB]) #[lddictP], -- [B7,B8]
    mkCase "ok/miss-quiet-preload-false" (#[.slice missSliceC]) #[lddictNQ], -- [B6,B7,B8,B9]
    mkCase "ok/miss-quiet-preload-true" (#[.slice missSliceTail1]) #[lddictPQ], -- [B8,B9]
    mkCase "err/present-missing-ref-nonquiet-preload-false" (#[.slice presentSliceNoRef]) #[lddictNP], -- [B4,B5]
    mkCase "err/present-missing-ref-nonquiet-preload-true" (#[.slice presentSliceNoRef]) #[lddictP], -- [B4,B5]
    mkCase "ok/present-missing-ref-quiet-preload-false" (#[.slice presentSliceNoRef]) #[lddictNQ], -- [B4,B6,B8]
    mkCase "ok/present-missing-ref-quiet-preload-true" (#[.slice presentSliceNoRef]) #[lddictPQ], -- [B4,B6,B8]
    mkCase "ok/present-prefix-preserve" (#[intV 7, .cell loadValueD, .slice presentSliceB]) #[lddictNP], -- [B1,B7,B10]
    mkCase "ok/miss-prefix-preserve" (#[intV (-3), .slice presentSliceA, .slice missSliceA]) #[lddictP], -- [B1,B8]
    mkCase "ok/quiet-prefix-preserve" (#[intV 55, .cell loadValueC, .slice missSliceC]) #[lddictNQ], -- [B1,B6,B9]
    mkCase "err/type-top-cell" (#[.cell loadValueA]) #[lddictNP], -- [B3]
    mkCase "err/type-top-builder" (#[.builder Builder.empty]) #[lddictNP], -- [B3]
    mkCaseCode "raw/decode-0xf404" #[] rawF404, -- [B10,B11]
    mkCaseCode "raw/decode-0xf405" #[] rawF405, -- [B10,B11]
    mkCaseCode "raw/decode-0xf406" #[] rawF406, -- [B10,B11]
    mkCaseCode "raw/decode-0xf407" #[] rawF407, -- [B10,B11]
    mkCaseCode "raw/decode-0xf408" #[] rawF408, -- [B11]
    mkCaseCode "raw/decode-0xf409" #[] rawF409, -- [B11]
    mkCaseCode "raw/decode-truncated" #[] rawF4, -- [B11]
    mkCase "gas/exact-nonquiet-preload-false"
      #[.slice presentSliceA]
      #[.pushInt (.num lddictGasNP), .tonEnvOp .setGasLimit, lddictNP]
      (oracleGasLimitsExact lddictGasNP), -- [B12]
    mkCase "gas/exact-minus-one-nonquiet-preload-false"
      #[.slice presentSliceA]
      #[.pushInt (.num lddictGasMinusOneNP), .tonEnvOp .setGasLimit, lddictNP]
      (oracleGasLimitsExactMinusOne lddictGasMinusOneNP), -- [B12]
    mkCase "gas/exact-quiet-preload-true"
      #[.slice presentSliceB]
      #[.pushInt (.num lddictGasPQ), .tonEnvOp .setGasLimit, lddictPQ]
      (oracleGasLimitsExact lddictGasPQ), -- [B12]
    mkCase "gas/exact-minus-one-quiet-preload-true"
      #[.slice presentSliceB]
      #[.pushInt (.num lddictGasMinusOnePQ), .tonEnvOp .setGasLimit, lddictPQ]
      (oracleGasLimitsExactMinusOne lddictGasMinusOnePQ) -- [B12]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genLddictqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.LDDICTQ
