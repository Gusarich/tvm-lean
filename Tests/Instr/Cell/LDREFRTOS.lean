import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDREFRTOS

/-
LDREFRTOS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LdrefRtos.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`LDREFRTOS` encode: `0xd5`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd5` decode to `.ldrefRtos`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_ref_rev_to_slice`, opcode `0xd5`)
  - and load helper `/Users/daniil/Coding/ton/crypto/vm/cells/CellSlice.cpp`
    (`load_cell_slice_ref`: cell-load gas; rejects special cells unless special-aware API is used).

Branch map used for this suite:
- Lean LDREFRTOS path: 6 branch sites / 8 terminal outcomes
  (opcode guard; pop-slice underflow/type; have-refs split; cell-load gas path;
   referenced-cell special split; success push order).
- C++ LDREFRTOS path (mode=0): aligned outcomes
  (`pop_cellslice`; `have_refs`; fetch ref; push remainder; `load_cell_slice_ref`;
   special-cell rejection as `cell_und` after remainder push).

Key risk areas:
- success order is `... remainder-slice loaded-ref-slice` (remainder below loaded);
- strict underflow/type ordering from `popSlice`;
- no-ref path is `cellUnd`;
- special referenced cell must fail with `cellUnd` after charging cell-load gas and
  after pushing remainder slice;
- decode/asm boundary is exact 8-bit opcode `0xd5`;
- gas edge behavior in oracle mode: exact succeeds, exact-minus-one fails.
-/

private def ldrefRtosId : InstrId := { name := "LDREFRTOS" }

private def ldrefRtosInstr : Instr := .ldrefRtos

private def mkLdrefRtosCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldrefRtosInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldrefRtosId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdrefRtosDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLdrefRtos ldrefRtosInstr stack

private def runLdrefRtosDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLdrefRtos .add (VM.push (intV 542)) stack

private def runLdrefRtosRaw (stack : Array Value) : Except Excno Unit × Array Value :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrCellLdrefRtos ldrefRtosInstr (pure ())).run st0
  (res, st1.stack)

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

private def ldrefRtosSetGasExact : Int :=
  -- `LDREFRTOS` loads referenced cell as slice (`load_cell_slice_ref`), charging cell-load gas.
  computeExactGasBudgetWithExtra ldrefRtosInstr cellLoadGasPrice

private def ldrefRtosSetGasExactMinusOne : Int :=
  if ldrefRtosSetGasExact > 0 then ldrefRtosSetGasExact - 1 else 0

private def patternedBits (n : Nat) (offset : Nat := 0) : BitString := Id.run do
  let mut out : BitString := #[]
  for i in [0:n] do
    out := out.push (((i + offset) % 2) = 1)
  out

private def refOrdA : Cell :=
  Cell.mkOrdinary (patternedBits 3) #[]

private def refOrdB : Cell :=
  Cell.mkOrdinary (patternedBits 6 1) #[Cell.ofUInt 1 1]

private def refOrdC : Cell :=
  Cell.mkOrdinary #[] #[Cell.ofUInt 4 11]

private def refOrdD : Cell :=
  Cell.mkOrdinary (patternedBits 2 1) #[Cell.empty, Cell.ofUInt 2 2]

private def refOrdE : Cell :=
  Cell.mkOrdinary (patternedBits 9 2) #[]

private def ordinaryRefPool : Array Cell :=
  #[refOrdA, refOrdB, refOrdC, refOrdD, refOrdE, Cell.empty]

private def specialLibraryCell : Cell :=
  -- Type byte `2` (library), then 256-bit hash payload.
  { bits := natToBits 2 8 ++ Array.replicate 256 false
    refs := #[]
    special := true
    levelMask := 0 }

private def parentBitsPool : Array BitString :=
  #[#[], patternedBits 1, patternedBits 3 1, patternedBits 5 2, patternedBits 8 3]

private def pickParentBits (rng : StdGen) : BitString × StdGen :=
  let (idx, rng') := randNat rng 0 (parentBitsPool.size - 1)
  (parentBitsPool[idx]!, rng')

private def pickOrdinaryRef (rng : StdGen) : Cell × StdGen :=
  let (idx, rng') := randNat rng 0 (ordinaryRefPool.size - 1)
  (ordinaryRefPool[idx]!, rng')

private def mkParentSlice (bits : BitString) (refs : Array Cell) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def expectedLdrefRtosStack (below : Array Value) (s : Slice) : Array Value :=
  let c := s.cell.refs[s.refPos]!
  let rest := { s with refPos := s.refPos + 1 }
  below ++ #[.slice rest, .slice (Slice.ofCell c)]

private def sOneRefA : Slice :=
  mkParentSlice (patternedBits 1) #[refOrdA]

private def sOneRefB : Slice :=
  mkParentSlice (patternedBits 3 1) #[refOrdB]

private def sTwoRefsAB : Slice :=
  mkParentSlice (patternedBits 5 2) #[refOrdA, refOrdB]

private def sTwoRefsCD : Slice :=
  mkParentSlice (patternedBits 8 3) #[refOrdC, refOrdD]

private def sThreeRefs : Slice :=
  mkParentSlice #[] #[refOrdD, refOrdB, refOrdE]

private def sNoRefsEmpty : Slice :=
  Slice.ofCell Cell.empty

private def sNoRefsBits : Slice :=
  Slice.ofCell (Cell.ofUInt 8 173)

private def sSpecialFirst : Slice :=
  mkParentSlice (patternedBits 4 1) #[specialLibraryCell, refOrdA]

private def genLdrefRtosFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  if shape = 0 then
    let (bits, rng2) := pickParentBits rng1
    let (r0, rng3) := pickOrdinaryRef rng2
    (mkLdrefRtosCase s!"fuzz/ok/one-ref/bits-{bits.size}" #[.slice (mkParentSlice bits #[r0])], rng3)
  else if shape = 1 then
    let (bits, rng2) := pickParentBits rng1
    let (r0, rng3) := pickOrdinaryRef rng2
    let (r1, rng4) := pickOrdinaryRef rng3
    (mkLdrefRtosCase s!"fuzz/ok/two-refs/bits-{bits.size}" #[.slice (mkParentSlice bits #[r0, r1])], rng4)
  else if shape = 2 then
    let (bits, rng2) := pickParentBits rng1
    let (r0, rng3) := pickOrdinaryRef rng2
    let (r1, rng4) := pickOrdinaryRef rng3
    let (r2, rng5) := pickOrdinaryRef rng4
    (mkLdrefRtosCase s!"fuzz/ok/three-refs/bits-{bits.size}" #[.slice (mkParentSlice bits #[r0, r1, r2])], rng5)
  else if shape = 3 then
    let (bits, rng2) := pickParentBits rng1
    let (r0, rng3) := pickOrdinaryRef rng2
    (mkLdrefRtosCase s!"fuzz/ok/deep-null/bits-{bits.size}"
      #[.null, .slice (mkParentSlice bits #[r0])], rng3)
  else if shape = 4 then
    let (bits, rng2) := pickParentBits rng1
    let (r0, rng3) := pickOrdinaryRef rng2
    (mkLdrefRtosCase s!"fuzz/ok/deep-int/bits-{bits.size}"
      #[intV 11, .slice (mkParentSlice bits #[r0])], rng3)
  else if shape = 5 then
    let (bits, rng2) := pickParentBits rng1
    (mkLdrefRtosCase s!"fuzz/cellund/no-refs/bits-{bits.size}" #[.slice (mkParentSlice bits #[])], rng2)
  else if shape = 6 then
    (mkLdrefRtosCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 7 then
    (mkLdrefRtosCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 8 then
    (mkLdrefRtosCase "fuzz/type/top-int" #[intV 19], rng1)
  else if shape = 9 then
    (mkLdrefRtosCase "fuzz/type/top-cell" #[.cell refOrdB], rng1)
  else if shape = 10 then
    (mkLdrefRtosCase "fuzz/type/top-builder-empty" #[.builder Builder.empty], rng1)
  else if shape = 11 then
    let (bits, rng2) := pickParentBits rng1
    let (r1, rng3) := pickOrdinaryRef rng2
    let s := mkParentSlice bits #[specialLibraryCell, r1]
    (mkLdrefRtosCase s!"fuzz/special/first-ref-cellund/bits-{bits.size}" #[.slice s], rng3)
  else if shape = 12 then
    let (bits, rng2) := pickParentBits rng1
    let (r1, rng3) := pickOrdinaryRef rng2
    let s := mkParentSlice bits #[specialLibraryCell, r1]
    (mkLdrefRtosCase s!"fuzz/special/deep-first-ref-cellund/bits-{bits.size}" #[.null, .slice s], rng3)
  else if shape = 13 then
    let (bits, rng2) := pickParentBits rng1
    let s := mkParentSlice bits #[] -- oracle-serializable full slice, but no refs at runtime
    (mkLdrefRtosCase s!"fuzz/cellund/deep-no-refs/bits-{bits.size}" #[.null, .slice s], rng2)
  else if shape = 14 then
    (mkLdrefRtosCase "fuzz/type/deep-top-not-slice" #[.slice sOneRefA, .null], rng1)
  else if shape = 15 then
    let (bits, rng2) := pickParentBits rng1
    (mkLdrefRtosCase s!"fuzz/type/deep-top-cell/bits-{bits.size}"
      #[.slice (mkParentSlice bits #[refOrdA]), .cell refOrdC], rng2)
  else
    let (bits, rng2) := pickParentBits rng1
    (mkLdrefRtosCase s!"fuzz/type/deep-top-builder/bits-{bits.size}"
      #[.slice (mkParentSlice bits #[refOrdA]), .builder Builder.empty], rng2)

def suite : InstrSuite where
  id := ldrefRtosId
  unit := #[
    { name := "unit/direct/success-order-and-ref-cursor"
      run := do
        expectOkStack "ok/one-ref-a"
          (runLdrefRtosDirect #[.slice sOneRefA])
          (expectedLdrefRtosStack #[] sOneRefA)

        expectOkStack "ok/two-refs-first-loaded"
          (runLdrefRtosDirect #[.slice sTwoRefsAB])
          (expectedLdrefRtosStack #[] sTwoRefsAB)

        let sPartial : Slice := { sThreeRefs with refPos := 1 }
        expectOkStack "ok/partial-slice-refpos1-loads-second"
          (runLdrefRtosDirect #[.slice sPartial])
          (expectedLdrefRtosStack #[] sPartial)

        expectOkStack "ok/deep-stack-preserve-below"
          (runLdrefRtosDirect #[.null, intV 7, .slice sTwoRefsCD])
          (expectedLdrefRtosStack #[.null, intV 7] sTwoRefsCD) }
    ,
    { name := "unit/direct/underflow-type-and-no-range-outcome"
      run := do
        expectErr "underflow/empty" (runLdrefRtosDirect #[]) .stkUnd

        expectErr "type/top-null"
          (runLdrefRtosDirect #[.null]) .typeChk
        expectErr "type/top-int"
          (runLdrefRtosDirect #[intV 13]) .typeChk
        expectErr "type/top-int-nan"
          (runLdrefRtosDirect #[.int .nan]) .typeChk
        expectErr "type/top-cell"
          (runLdrefRtosDirect #[.cell refOrdA]) .typeChk
        expectErr "type/top-builder-empty"
          (runLdrefRtosDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdrefRtosDirect #[.slice sOneRefA, .null]) .typeChk

        -- LDREFRTOS has no dedicated `.rangeChk` branch; malformed inputs map to type/cell underflow.
        expectErr "cellund/no-refs-empty-cell"
          (runLdrefRtosDirect #[.slice sNoRefsEmpty]) .cellUnd
        expectErr "cellund/no-refs-nonempty-cell"
          (runLdrefRtosDirect #[.slice sNoRefsBits]) .cellUnd }
    ,
    { name := "unit/direct/special-ref-cellund-after-remainder-push"
      run := do
        let expectedRestVal : Value := .slice { sSpecialFirst with refPos := sSpecialFirst.refPos + 1 }

        let (res0, st0) := runLdrefRtosRaw #[.slice sSpecialFirst]
        match res0 with
        | .error .cellUnd =>
            if st0 == #[expectedRestVal] then
              pure ()
            else
              throw (IO.userError s!"special/no-below: expected stack {reprStr #[expectedRestVal]}, got {reprStr st0}")
        | .error e =>
            throw (IO.userError s!"special/no-below: expected cellUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "special/no-below: expected cellUnd, got success")

        let (res1, st1) := runLdrefRtosRaw #[.null, .slice sSpecialFirst]
        match res1 with
        | .error .cellUnd =>
            let expected := #[.null, expectedRestVal]
            if st1 == expected then
              pure ()
            else
              throw (IO.userError s!"special/with-below: expected stack {reprStr expected}, got {reprStr st1}")
        | .error e =>
            throw (IO.userError s!"special/with-below: expected cellUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "special/with-below: expected cellUnd, got success") }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[ldrefRtosInstr, .ldref, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldrefrtos-d5" s0 ldrefRtosInstr 8
        let s2 ← expectDecodeStep "decode/ldref-d4" s1 .ldref 8
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-ldrefrtos-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLdrefRtosDispatchFallback #[.null])
          #[.null, intV 542] }
  ]
  oracle := #[
    mkLdrefRtosCase "ok/one-ref-a" #[.slice sOneRefA],
    mkLdrefRtosCase "ok/one-ref-b" #[.slice sOneRefB],
    mkLdrefRtosCase "ok/two-refs-a-b" #[.slice sTwoRefsAB],
    mkLdrefRtosCase "ok/two-refs-c-d" #[.slice sTwoRefsCD],
    mkLdrefRtosCase "ok/three-refs" #[.slice sThreeRefs],
    mkLdrefRtosCase "ok/deep-stack-null" #[.null, .slice sOneRefA],
    mkLdrefRtosCase "ok/deep-stack-int-null" #[intV 5, .null, .slice sTwoRefsAB],
    mkLdrefRtosCase "ok/child-empty-ref" #[.slice (mkParentSlice (patternedBits 2 1) #[Cell.empty])],
    mkLdrefRtosCase "ok/child-with-two-refs"
      #[.slice (mkParentSlice (patternedBits 3 2) #[Cell.mkOrdinary (patternedBits 1) #[Cell.empty, refOrdA]])],
    mkLdrefRtosCase "ok/parent-zero-bits" #[.slice (mkParentSlice #[] #[refOrdD])],
    mkLdrefRtosCase "ok/parent-nonzero-bits" #[.slice (mkParentSlice (patternedBits 8 2) #[refOrdE])],
    mkLdrefRtosCase "ok/with-builder-below" #[.builder Builder.empty, .slice sOneRefA],

    mkLdrefRtosCase "cellund/no-refs-empty" #[.slice sNoRefsEmpty],
    mkLdrefRtosCase "cellund/no-refs-bits" #[.slice sNoRefsBits],
    mkLdrefRtosCase "cellund/no-refs-deep" #[.null, .slice sNoRefsBits],

    mkLdrefRtosCase "underflow/empty" #[],
    mkLdrefRtosCase "type/top-null" #[.null],
    mkLdrefRtosCase "type/top-int" #[intV 17],
    mkLdrefRtosCase "type/top-cell" #[.cell refOrdA],
    mkLdrefRtosCase "type/top-builder-empty" #[.builder Builder.empty],
    mkLdrefRtosCase "type/deep-top-not-slice" #[.slice sOneRefA, .null],
    mkLdrefRtosCase "type/deep-top-cell" #[.slice sOneRefA, .cell refOrdB],

    mkLdrefRtosCase "special/first-ref-cellund" #[.slice sSpecialFirst],
    mkLdrefRtosCase "special/first-ref-cellund-with-below" #[.null, .slice sSpecialFirst],

    mkLdrefRtosCase "gas/exact-cost-succeeds" #[.slice sOneRefA]
      #[.pushInt (.num ldrefRtosSetGasExact), .tonEnvOp .setGasLimit, ldrefRtosInstr],
    mkLdrefRtosCase "gas/exact-minus-one-out-of-gas" #[.slice sOneRefA]
      #[.pushInt (.num ldrefRtosSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldrefRtosInstr]
  ]
  fuzz := #[
    { seed := 2026021011
      count := 320
      gen := genLdrefRtosFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDREFRTOS
