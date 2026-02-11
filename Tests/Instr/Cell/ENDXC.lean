import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.ENDXC

/-
ENDXC branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.endxc`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf23` decode to `.cellOp .endxc`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.cellOp .endxc` encode as `0xcf23`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_builder_to_special_cell`, opcode `0xcf23`).

Branch map used for this suite:
- dispatch guard in instruction-local handler (`.cellOp .endxc` vs fallback);
- `checkUnderflow 2` then pop order: `special` (bool/int) first, `builder` second;
- finalize split: `special=false` => ordinary finalize; `special=true` => exotic validation;
- gas charge (`cellCreateGasPrice`) occurs after stack/type checks and before `finalizeCopy`,
  including failing special validation.
-/

private def endxcId : InstrId := { name := "ENDXC" }

private def endxcInstr : Instr := .cellOp .endxc

private def strefRqInstr : Instr := .cellOp (.strefR true)

private def bdepthInstr : Instr := .cellOp .bdepth

private def endxcOpcode : Nat := 0xcf23

private def dispatchSentinel : Int := Int.ofNat endxcOpcode

private def execInstrCellOpEndxcOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp .endxc => execCellOpExt .endxc next
  | _ => next

private def mkEndxcCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[endxcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := endxcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkEndxcProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := endxcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runEndxcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpEndxcOnly endxcInstr stack

private def runEndxcDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpEndxcOnly instr (VM.push (intV dispatchSentinel)) stack

private def runEndxcRaw (stack : Array Value) : Except Excno Unit × Array Value × Int :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      gas := GasLimits.ofLimit 10_000 }
  let (res, st1) := (execInstrCellOpEndxcOnly endxcInstr (pure ())).run st0
  (res, st1.stack, st1.gas.gasConsumed)

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

private def endxcSetGasExact : Int :=
  computeExactGasBudgetWithExtra endxcInstr cellCreateGasPrice

private def endxcSetGasExactMinusOne : Int :=
  if endxcSetGasExact > 0 then endxcSetGasExact - 1 else 0

private def libraryBits (hash : Nat) : BitString :=
  natToBits 2 8 ++ natToBits hash 256

private def merkleProofBits (hash depth : Nat) : BitString :=
  natToBits 3 8 ++ natToBits hash 256 ++ natToBits depth 16

private def emptyRefHashNat : Nat :=
  bytesToNatBE (Cell.hashBytes Cell.empty)

private def emptyRefDepthNat : Nat :=
  Cell.empty.depth

private def wrongHashNat : Nat :=
  if emptyRefHashNat = 0 then 1 else 0

private def wrongDepthNat : Nat :=
  if emptyRefDepthNat < 65535 then emptyRefDepthNat + 1 else emptyRefDepthNat - 1

private def leafA : Cell := Cell.ofUInt 1 1
private def leafB : Cell := Cell.ofUInt 3 2

private def ordinaryBuilderSample : Builder :=
  { bits := natToBits 0x15 5
    refs := #[leafA, leafB] }

private def libraryBuilder0 : Builder :=
  { bits := libraryBits 0
    refs := #[] }

private def libraryBuilderA5 : Builder :=
  { bits := libraryBits 0xA5
    refs := #[] }

private def merkleProofBuilderValid : Builder :=
  { bits := merkleProofBits emptyRefHashNat emptyRefDepthNat
    refs := #[Cell.empty] }

private def invalidSpecialType0Builder : Builder :=
  { bits := natToBits 0 8
    refs := #[] }

private def invalidSpecialShortBuilder : Builder :=
  { bits := natToBits 1 7
    refs := #[] }

private def invalidLibraryLenBuilder : Builder :=
  { bits := natToBits 2 8 ++ natToBits 0 255
    refs := #[] }

private def invalidLibraryWithRefBuilder : Builder :=
  { bits := libraryBits 0
    refs := #[Cell.empty] }

private def invalidMerkleHashBuilder : Builder :=
  { bits := merkleProofBits wrongHashNat emptyRefDepthNat
    refs := #[Cell.empty] }

private def invalidMerkleDepthBuilder : Builder :=
  { bits := merkleProofBits emptyRefHashNat wrongDepthNat
    refs := #[Cell.empty] }

private def appendOneEmptyCellRefToTopBuilder : Array Instr :=
  #[.newc, .endc, .xchg0 1, .stref]

private def appendRefsToTopBuilder : Nat → Array Instr
  | 0 => #[]
  | n + 1 => appendRefsToTopBuilder n ++ appendOneEmptyCellRefToTopBuilder

private def mkOrdinaryBuilderProgram
    (bits refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkLibraryBuilderProgram (hash : Nat) (refs : Nat := 0) : Array Instr :=
  #[.newc,
    .pushInt (.num 2), .xchg0 1, .stu 8,
    .pushInt (.num (Int.ofNat hash)), .xchg0 1, .stu 256]
    ++ appendRefsToTopBuilder refs

private def mkMerkleProofBuilderProgram (hash depth : Nat) (refs : Nat := 1) : Array Instr :=
  #[.newc,
    .pushInt (.num 3), .xchg0 1, .stu 8,
    .pushInt (.num (Int.ofNat hash)), .xchg0 1, .stu 256,
    .pushInt (.num (Int.ofNat depth)), .xchg0 1, .stu 16]
    ++ appendRefsToTopBuilder refs

private def withEndxcFlag (builderProgram : Array Instr) (flag : IntVal) : Array Instr :=
  builderProgram ++ #[.pushInt flag, endxcInstr]

private def endxcProgramFalseBits1 : Array Instr :=
  withEndxcFlag (mkOrdinaryBuilderProgram 1 0 (.num 1)) (.num 0)

private def endxcProgramFalseBits256 : Array Instr :=
  withEndxcFlag (mkOrdinaryBuilderProgram 256 0 (.num 0xA5)) (.num 0)

private def endxcProgramFalseBits1023Refs4 : Array Instr :=
  withEndxcFlag (mkOrdinaryBuilderProgram 1023 4) (.num 0)

private def endxcProgramTrueLibrary0 : Array Instr :=
  withEndxcFlag (mkLibraryBuilderProgram 0) (.num (-1))

private def endxcProgramTrueLibraryA5 : Array Instr :=
  withEndxcFlag (mkLibraryBuilderProgram 0xA5) (.num (-1))

private def endxcProgramTrueLibraryFlag7 : Array Instr :=
  withEndxcFlag (mkLibraryBuilderProgram 1) (.num 7)

private def endxcProgramTrueMerkleProofValid : Array Instr :=
  withEndxcFlag (mkMerkleProofBuilderProgram emptyRefHashNat emptyRefDepthNat 1) (.num (-1))

private def endxcProgramFalseType0Payload : Array Instr :=
  withEndxcFlag #[.newc, .pushInt (.num 0), .xchg0 1, .stu 8] (.num 0)

private def endxcProgramTrueType0Payload : Array Instr :=
  withEndxcFlag #[.newc, .pushInt (.num 0), .xchg0 1, .stu 8] (.num (-1))

private def endxcProgramTrueShortBits7 : Array Instr :=
  withEndxcFlag #[.newc, .pushInt (.num 1), .xchg0 1, .stu 7] (.num (-1))

private def endxcProgramTrueLibraryLen255 : Array Instr :=
  withEndxcFlag
    #[.newc,
      .pushInt (.num 2), .xchg0 1, .stu 8,
      .pushInt (.num 0), .xchg0 1, .stu 255]
    (.num (-1))

private def endxcProgramTrueLibraryWithRef : Array Instr :=
  withEndxcFlag (mkLibraryBuilderProgram 0 1) (.num (-1))

private def endxcProgramTrueMerkleProofBadHash : Array Instr :=
  withEndxcFlag (mkMerkleProofBuilderProgram wrongHashNat emptyRefDepthNat 1) (.num (-1))

def suite : InstrSuite where
  id := endxcId
  unit := #[
    { name := "unit/direct/success-ordinary-vs-special"
      run := do
        expectOkStack "ok/false-empty-builder"
          (runEndxcDirect #[.builder Builder.empty, intV 0])
          #[.cell Cell.empty]

        expectOkStack "ok/false-preserve-bits-and-refs"
          (runEndxcDirect #[.builder ordinaryBuilderSample, intV 0])
          #[.cell ordinaryBuilderSample.finalize]

        let expectedLib ←
          match libraryBuilder0.finalizeCopy true with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"expected library finalizeCopy(true) success, got {e}")
        expectOkStack "ok/true-library-cell"
          (runEndxcDirect #[.builder libraryBuilder0, intV (-1)])
          #[.cell expectedLib]

        let expectedMerkle ←
          match merkleProofBuilderValid.finalizeCopy true with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"expected merkle-proof finalizeCopy(true) success, got {e}")
        expectOkStack "ok/true-merkle-proof-cell"
          (runEndxcDirect #[.builder merkleProofBuilderValid, intV (-1)])
          #[.cell expectedMerkle]

        expectOkStack "ok/deep-stack-nonzero-flag-is-true"
          (runEndxcDirect #[.null, intV 5, .builder libraryBuilderA5, intV 7])
          #[.null, intV 5, .cell (←
            match libraryBuilderA5.finalizeCopy true with
            | .ok c => pure c
            | .error e => throw (IO.userError s!"libraryBuilderA5 finalizeCopy(true) failed: {e}")
          )] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty"
          (runEndxcDirect #[]) .stkUnd
        expectErr "underflow/one-builder"
          (runEndxcDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-int"
          (runEndxcDirect #[intV 0]) .stkUnd

        expectErr "type/top-not-int-null"
          (runEndxcDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/top-not-int-cell"
          (runEndxcDirect #[.builder Builder.empty, .cell Cell.empty]) .typeChk
        expectErr "intov/top-nan"
          (runEndxcDirect #[.builder Builder.empty, .int .nan]) .intOv
        expectErr "type/second-not-builder-null"
          (runEndxcDirect #[.null, intV 0]) .typeChk
        expectErr "type/second-not-builder-cell"
          (runEndxcDirect #[.cell Cell.empty, intV 0]) .typeChk }
    ,
    { name := "unit/direct/special-validation-errors"
      run := do
        expectErr "cellov/true-type0-ordinary"
          (runEndxcDirect #[.builder invalidSpecialType0Builder, intV (-1)]) .cellOv
        expectErr "cellov/true-short-7-bits"
          (runEndxcDirect #[.builder invalidSpecialShortBuilder, intV (-1)]) .cellOv
        expectErr "cellov/true-library-len-255"
          (runEndxcDirect #[.builder invalidLibraryLenBuilder, intV (-1)]) .cellOv
        expectErr "cellov/true-library-with-ref"
          (runEndxcDirect #[.builder invalidLibraryWithRefBuilder, intV (-1)]) .cellOv
        expectErr "cellov/true-merkle-hash-mismatch"
          (runEndxcDirect #[.builder invalidMerkleHashBuilder, intV (-1)]) .cellOv
        expectErr "cellov/true-merkle-depth-mismatch"
          (runEndxcDirect #[.builder invalidMerkleDepthBuilder, intV (-1)]) .cellOv

        -- The same payload is accepted when `special=false` (ordinary finalization path).
        expectOkStack "ok/false-type0-payload-is-ordinary-cell"
          (runEndxcDirect #[.builder invalidSpecialType0Builder, intV 0])
          #[.cell invalidSpecialType0Builder.finalize] }
    ,
    { name := "unit/gas/cell-create-charge-on-finalize-attempt"
      run := do
        let (r0, st0, gas0) := runEndxcRaw #[.builder Builder.empty, intV 0]
        match r0 with
        | .ok _ =>
            if gas0 = cellCreateGasPrice then
              pure ()
            else
              throw (IO.userError s!"gas/false-success: expected {cellCreateGasPrice}, got {gas0}")
        | .error e =>
            throw (IO.userError s!"gas/false-success: expected success, got {e}")
        if st0 == #[.cell Cell.empty] then
          pure ()
        else
          throw (IO.userError s!"gas/false-success: expected stack #[.cell Cell.empty], got {reprStr st0}")

        let (r1, _st1, gas1) := runEndxcRaw #[.builder libraryBuilder0, intV (-1)]
        match r1 with
        | .ok _ =>
            if gas1 = cellCreateGasPrice then
              pure ()
            else
              throw (IO.userError s!"gas/true-success: expected {cellCreateGasPrice}, got {gas1}")
        | .error e =>
            throw (IO.userError s!"gas/true-success: expected success, got {e}")

        let (r2, st2, gas2) := runEndxcRaw #[.builder invalidSpecialType0Builder, intV (-1)]
        match r2 with
        | .error .cellOv =>
            if gas2 = cellCreateGasPrice then
              pure ()
            else
              throw (IO.userError s!"gas/true-fail-cellov: expected {cellCreateGasPrice}, got {gas2}")
        | .error e =>
            throw (IO.userError s!"gas/true-fail-cellov: expected cellOv, got {e}")
        | .ok _ =>
            throw (IO.userError "gas/true-fail-cellov: expected failure, got success")
        if st2.isEmpty then
          pure ()
        else
          throw (IO.userError s!"gas/true-fail-cellov: expected empty stack after pops, got {reprStr st2}")

        let (r3, st3, gas3) := runEndxcRaw #[.builder Builder.empty, .null]
        match r3 with
        | .error .typeChk =>
            if gas3 = 0 then
              pure ()
            else
              throw (IO.userError s!"gas/type-before-finalize: expected 0, got {gas3}")
        | .error e =>
            throw (IO.userError s!"gas/type-before-finalize: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "gas/type-before-finalize: expected failure, got success")
        if st3 == #[.builder Builder.empty] then
          pure ()
        else
          throw (IO.userError s!"gas/type-before-finalize: expected builder to remain, got {reprStr st3}")

        let (r4, st4, gas4) := runEndxcRaw #[.null, intV 0]
        match r4 with
        | .error .typeChk =>
            if gas4 = 0 then
              pure ()
            else
              throw (IO.userError s!"gas/order-bool-then-builder: expected 0, got {gas4}")
        | .error e =>
            throw (IO.userError s!"gas/order-bool-then-builder: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "gas/order-bool-then-builder: expected failure, got success")
        if st4.isEmpty then
          pure ()
        else
          throw (IO.userError s!"gas/order-bool-then-builder: expected empty stack after bool+builder pops, got {reprStr st4}") }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let canonical ←
          match assembleCp0 [endxcInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/canonical failed: {e}")
        if canonical.bits = natToBits endxcOpcode 16 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/canonical: expected opcode 0xcf23, got bits {canonical.bits}")

        let program : Array Instr :=
          #[.endc, strefRqInstr, endxcInstr, bdepthInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/endc-8bit-neighbor" s0 .endc 8
        let s2 ← expectDecodeStep "decode/strefrq-neighbor" s1 strefRqInstr 16
        let s3 ← expectDecodeStep "decode/endxc" s2 endxcInstr 16
        let s4 ← expectDecodeStep "decode/bdepth-neighbor" s3 bdepthInstr 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/sequence-end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xc9 8
            ++ natToBits 0xcf1c 16
            ++ natToBits endxcOpcode 16
            ++ natToBits 0xcf30 16
            ++ addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-endc" r0 .endc 8
        let r2 ← expectDecodeStep "decode/raw-strefrq" r1 strefRqInstr 16
        let r3 ← expectDecodeStep "decode/raw-endxc" r2 endxcInstr 16
        let r4 ← expectDecodeStep "decode/raw-bdepth" r3 bdepthInstr 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-endxc-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop-add"
          (runEndxcDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-bdepth"
          (runEndxcDispatchFallback bdepthInstr #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel] }
  ]
  oracle := #[
    mkEndxcCase "ok/direct/false-empty-builder"
      #[.builder Builder.empty, intV 0],
    mkEndxcCase "ok/direct/deep-stack-false-empty-builder"
      #[.null, .builder Builder.empty, intV 0],

    mkEndxcProgramCase "ok/program/false-bits1"
      #[]
      endxcProgramFalseBits1,
    mkEndxcProgramCase "ok/program/false-bits256"
      #[]
      endxcProgramFalseBits256,
    mkEndxcProgramCase "ok/program/false-bits1023-refs4"
      #[]
      endxcProgramFalseBits1023Refs4,
    mkEndxcProgramCase "ok/program/true-library-hash0"
      #[]
      endxcProgramTrueLibrary0,
    mkEndxcProgramCase "ok/program/true-library-hash-a5"
      #[]
      endxcProgramTrueLibraryA5,
    mkEndxcProgramCase "ok/program/true-library-flag7"
      #[]
      endxcProgramTrueLibraryFlag7,
    mkEndxcProgramCase "ok/program/true-merkle-proof-valid"
      #[]
      endxcProgramTrueMerkleProofValid,
    mkEndxcProgramCase "ok/program/false-type0-payload-allowed"
      #[]
      endxcProgramFalseType0Payload,

    mkEndxcCase "underflow/empty" #[],
    mkEndxcCase "underflow/one-builder" #[.builder Builder.empty],
    mkEndxcCase "type/top-not-int-null" #[.builder Builder.empty, .null],
    mkEndxcCase "type/top-not-int-cell" #[.builder Builder.empty, .cell Cell.empty],
    mkEndxcCase "type/second-not-builder-null" #[.null, intV 0],
    mkEndxcCase "type/second-not-builder-cell" #[.cell Cell.empty, intV 0],

    mkEndxcCase "cellov/direct/true-empty-builder" #[.builder Builder.empty, intV (-1)],
    mkEndxcProgramCase "cellov/program/true-type0-payload"
      #[]
      endxcProgramTrueType0Payload,
    mkEndxcProgramCase "cellov/program/true-short-bits7"
      #[]
      endxcProgramTrueShortBits7,
    mkEndxcProgramCase "cellov/program/true-library-len255"
      #[]
      endxcProgramTrueLibraryLen255,
    mkEndxcProgramCase "cellov/program/true-library-with-ref"
      #[]
      endxcProgramTrueLibraryWithRef,
    mkEndxcProgramCase "cellov/program/true-merkle-proof-bad-hash"
      #[]
      endxcProgramTrueMerkleProofBadHash,

    mkEndxcCase "gas/exact-cost-succeeds"
      #[.builder Builder.empty, intV 0]
      #[.pushInt (.num endxcSetGasExact), .tonEnvOp .setGasLimit, endxcInstr],
    mkEndxcCase "gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty, intV 0]
      #[.pushInt (.num endxcSetGasExactMinusOne), .tonEnvOp .setGasLimit, endxcInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.ENDXC
