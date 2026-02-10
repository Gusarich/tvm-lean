import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDEMPTY

/-
SDEMPTY branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Sdempty.lean` (`.sdempty`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc701` decode to `.sdempty`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sdempty` assembles to `0xc701`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`reg_un_cs_cmp(..., 0xc701, "SDEMPTY", [](cs){ return cs->empty(); })`).

Branch map used for this suite:
- dispatch guard (`.sdempty` vs `next`);
- operand fetch via `popSlice`: `stkUnd` / `typeChk` / success;
- success predicate split on `s.bitsRemaining == 0`:
  `-1` when no bits remain, `0` otherwise (refs are intentionally ignored).
-/

private def sdemptyId : InstrId := { name := "SDEMPTY" }

private def sdemptyInstr : Instr := .sdempty

private def sdemptyWord : Nat := 0xc701

private def dispatchSentinel : Int := 1701

private def mkSdemptyCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdemptyInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdemptyId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdemptyDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdempty sdemptyInstr stack

private def runSdemptyDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdempty instr (VM.push (intV dispatchSentinel)) stack

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkSliceWithSize (bits refs : Nat) (phase : Nat := 0) : Slice :=
  let refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
  let refLeafB : Cell := Cell.mkOrdinary (natToBits 9 4) #[]
  let refLeafC : Cell := Cell.mkOrdinary (natToBits 6 3) #[]
  let refLeafD : Cell := Cell.mkOrdinary (natToBits 0x2d 6) #[refLeafA]
  let refPool : Array Cell := #[refLeafA, refLeafB, refLeafC, refLeafD]
  let pickedRefs : Array Cell :=
    Array.ofFn (n := refs) fun i => refPool[i.1 % refPool.size]!
  mkSliceWithBitsRefs (stripeBits bits phase) pickedRefs

private def sdemptySetGasExact : Int :=
  computeExactGasBudget sdemptyInstr

private def sdemptySetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdemptyInstr

def suite : InstrSuite where
  id := sdemptyId
  unit := #[
    { name := "unit/direct/returns-minus1-when-no-bits-remain"
      run := do
        let partialA : Slice :=
          { cell := (Cell.mkOrdinary (stripeBits 19 0) #[Cell.empty, Cell.empty])
            bitPos := 19
            refPos := 0 }
        let partialB : Slice :=
          { cell := (Cell.mkOrdinary (stripeBits 23 1) #[Cell.empty, Cell.empty, Cell.empty])
            bitPos := 23
            refPos := 2 }
        let partialC : Slice :=
          { cell := (Cell.mkOrdinary (stripeBits 1023 0) #[])
            bitPos := 1023
            refPos := 0 }
        let checks : Array Slice :=
          #[
            mkSliceWithSize 0 0,
            mkSliceWithSize 0 1,
            mkSliceWithSize 0 4,
            partialA,
            partialB,
            partialC
          ]
        for s in checks do
          expectOkStack s!"minus1/bits-{s.bitsRemaining}/refs-{s.refsRemaining}"
            (runSdemptyDirect #[.slice s]) #[intV (-1)] }
    ,
    { name := "unit/direct/returns-zero-when-any-bit-remains"
      run := do
        let partialA : Slice :=
          { cell := (Cell.mkOrdinary (stripeBits 9 0) #[Cell.empty])
            bitPos := 4
            refPos := 0 }
        let partialB : Slice :=
          { cell := (Cell.mkOrdinary (stripeBits 1023 1) #[Cell.empty, Cell.empty])
            bitPos := 1022
            refPos := 1 }
        let checks : Array Slice :=
          #[
            mkSliceWithSize 1 0,
            mkSliceWithSize 1 4,
            mkSliceWithSize 7 0,
            mkSliceWithSize 255 1,
            mkSliceWithSize 1023 4,
            partialA,
            partialB
          ]
        for s in checks do
          expectOkStack s!"zero/bits-{s.bitsRemaining}/refs-{s.refsRemaining}"
            (runSdemptyDirect #[.slice s]) #[intV 0] }
    ,
    { name := "unit/direct/preserves-below-stack"
      run := do
        let below : Array Value := #[.null, intV 9, .cell Cell.empty]
        let emptyBitsSlice := mkSliceWithSize 0 2
        expectOkStack "preserve/below-with-minus1"
          (runSdemptyDirect (below ++ #[.slice emptyBitsSlice]))
          (below ++ #[intV (-1)])

        let nonEmptyBitsSlice := mkSliceWithSize 8 1
        expectOkStack "preserve/below-with-zero"
          (runSdemptyDirect (below ++ #[.slice nonEmptyBitsSlice]))
          (below ++ #[intV 0]) }
    ,
    { name := "unit/direct/underflow-and-type-errors"
      run := do
        expectErr "underflow/empty" (runSdemptyDirect #[]) .stkUnd

        let bads : Array (String × Value) :=
          #[
            ("null", .null),
            ("int", intV 0),
            ("cell", .cell Cell.empty),
            ("builder", .builder Builder.empty),
            ("tuple", .tuple #[]),
            ("continuation", .cont (.quit 0))
          ]
        for bad in bads do
          let tag := bad.1
          let v := bad.2
          expectErr s!"type/{tag}" (runSdemptyDirect #[v]) .typeChk }
    ,
    { name := "unit/direct/error-order-top-first"
      run := do
        let validSlice := mkSliceWithSize 0 1
        expectErr "type/top-first-over-valid-slice"
          (runSdemptyDirect #[.slice validSlice, .null]) .typeChk
        expectOkStack "ok/top-slice-below-value-untouched"
          (runSdemptyDirect #[.null, .slice validSlice]) #[.null, intV (-1)] }
    ,
    { name := "unit/opcode/decode-assemble-and-dispatch"
      run := do
        let canonical ←
          match assembleCp0 [sdemptyInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assembleCp0 failed: {e}")
        if canonical.bits = natToBits sdemptyWord 16 then
          pure ()
        else
          throw (IO.userError s!"unexpected opcode bits: {reprStr canonical.bits}")

        let trioCode ←
          match assembleCp0 [.sempty, sdemptyInstr, .srempty] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble trio failed: {e}")
        let s0 := Slice.ofCell trioCode
        let s1 ← expectDecodeStep "decode/sempty" s0 .sempty 16
        let s2 ← expectDecodeStep "decode/sdempty" s1 sdemptyInstr 16
        let s3 ← expectDecodeStep "decode/srempty" s2 .srempty 16
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"expected no trailing bits, got {s3.bitsRemaining}")

        let raw := mkSliceFromBits (natToBits sdemptyWord 16 ++ natToBits 0xa5 8)
        let rest ← expectDecodeStep "decode/raw-word" raw sdemptyInstr 16
        if rest.readBits 8 = natToBits 0xa5 8 then
          pure ()
        else
          throw (IO.userError "decode/raw-word did not preserve trailing payload")

        expectOkStack "dispatch/fallback/non-sdempty"
          (runSdemptyDispatchFallback .add #[]) #[intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdemptyCase "ok/empty/bits0-refs0" #[.slice (mkSliceWithSize 0 0)],
    mkSdemptyCase "ok/empty/bits0-refs1" #[.slice (mkSliceWithSize 0 1)],
    mkSdemptyCase "ok/empty/bits0-refs4" #[.slice (mkSliceWithSize 0 4)],
    mkSdemptyCase "ok/empty/deep-below-null" #[.null, .slice (mkSliceWithSize 0 2)],
    mkSdemptyCase "ok/empty/deep-below-int" #[intV 77, .slice (mkSliceWithSize 0 3)],

    mkSdemptyCase "ok/nonempty/bits1-refs0" #[.slice (mkSliceWithSize 1 0)],
    mkSdemptyCase "ok/nonempty/bits1-refs4" #[.slice (mkSliceWithSize 1 4)],
    mkSdemptyCase "ok/nonempty/bits7-refs0" #[.slice (mkSliceWithSize 7 0)],
    mkSdemptyCase "ok/nonempty/bits8-refs2" #[.slice (mkSliceWithSize 8 2)],
    mkSdemptyCase "ok/nonempty/bits255-refs0" #[.slice (mkSliceWithSize 255 0)],
    mkSdemptyCase "ok/nonempty/bits256-refs1" #[.slice (mkSliceWithSize 256 1)],
    mkSdemptyCase "ok/nonempty/bits511-refs3" #[.slice (mkSliceWithSize 511 3)],
    mkSdemptyCase "ok/nonempty/bits1023-refs0" #[.slice (mkSliceWithSize 1023 0)],
    mkSdemptyCase "ok/nonempty/bits1023-refs4" #[.slice (mkSliceWithSize 1023 4)],
    mkSdemptyCase "ok/nonempty/deep-below-null" #[.null, .slice (mkSliceWithSize 16 1)],
    mkSdemptyCase "ok/nonempty/deep-below-int" #[intV 42, .slice (mkSliceWithSize 32 2)],

    mkSdemptyCase "underflow/empty-stack" #[],
    mkSdemptyCase "type/top-null" #[.null],
    mkSdemptyCase "type/top-int" #[intV 0],
    mkSdemptyCase "type/top-cell" #[.cell Cell.empty],
    mkSdemptyCase "type/top-builder" #[.builder Builder.empty],
    mkSdemptyCase "error-order/top-nonslice-over-valid-slice"
      #[.slice (mkSliceWithSize 0 1), .null],

    mkSdemptyCase "gas/exact-succeeds"
      #[.slice (mkSliceWithSize 1 0)]
      #[.pushInt (.num sdemptySetGasExact), .tonEnvOp .setGasLimit, sdemptyInstr],
    mkSdemptyCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkSliceWithSize 1 0)]
      #[.pushInt (.num sdemptySetGasExactMinusOne), .tonEnvOp .setGasLimit, sdemptyInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDEMPTY
