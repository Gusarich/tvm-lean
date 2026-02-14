import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.LDDICT

/-!
INSTRUCTION: LDDICT

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch path.
   - `execInstrDictLddict` handles only `.lddict` and all other instructions route to `next`.

2. [B2] Underflow/type errors (runtime preconditions).
   - Pop one item as a slice via `VM.popSlice`.
   - Empty stack -> `.stkUnd`.
   - Non-slice top value -> `.typeChk`.

3. [B3] Bit/ref availability checks before mutation.
   - Missing first bit (`haveBits 1 == false`) -> `.cellUnd`.
   - First bit is `1` but there is no required ref (`haveRefs 1 == false`) -> `.cellUnd`.

4. [B4] Non-preload present=0 success branch.
   - Pushes `.null` and pushes the remainder slice with `bitPos + 1`.
   - `refPos` does not move.

5. [B5] Non-preload present=1 success branch.
   - Pushes the reference at current `refPos`.
   - Pushes the remainder slice with `bitPos + 1` and `refPos + 1`.

6. [B6] Runtime shape difference of hit/miss for `.lddict` (preload=false, quiet=false).
   - Absent-key path pushes one stack value + remainder.
   - Present-key path pushes two stack values (`.cell`, remainder).
   - No status flag is ever pushed because `quiet=false`.

7. [B7] Decoder mapping and opcode boundaries.
   - `0xf404` decodes to `.lddict false false`.
   - `0xf405`, `0xf406`, `0xf407` decode to other `.lddict` variants.
   - Adjacent opcode `0xf403` decodes to `.dictExt (.lddicts false)`.
   - `0xf408` must not decode as `.lddict`.
   - Truncated 8-bit (`0xf4`) and 15-bit (`0xF404 >> 1`) forms are `invOpcode`.

8. [B8] Assembler encoding.
   - `.lddict false false` serializes to `0xf404`.
   - `.lddict true false`, `.lddict false true`, `.lddict true true` serializes to `0xf405..0xf407`.
   - No variable family for this opcode in assembler beyond valid flag combinations.

9. [B9] Gas accounting.
   - `gas = instrGas` with no explicit variable penalty for this opcode family.
   - exact-success and exact-minus-one tests are required.

TOTAL BRANCHES: 9

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by the fuzzer.
-/

private def lddictId : InstrId :=
  { name := "LDDICT" }

private def lddictInstr : Instr := .lddict false false

private def lddictDispatchSentinel : Int :=
  111_222_333

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw15 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 15) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def rawF404 : Cell := raw16 0xf404
private def rawF405 : Cell := raw16 0xf405
private def rawF406 : Cell := raw16 0xf406
private def rawF407 : Cell := raw16 0xf407
private def rawF403 : Cell := raw16 0xf403
private def rawF408 : Cell := raw16 0xf408
private def rawF4 : Cell := raw8 0xf4
private def raw15Inv : Cell := raw15 (0xf404 >>> 1)

private def valueCellA : Cell := Cell.mkOrdinary (natToBits 0xA5 8) #[]
private def valueCellB : Cell := Cell.mkOrdinary (natToBits 0xB5 8) #[]
private def valueCellC : Cell := Cell.mkOrdinary (natToBits 0xC5 8) #[]

private def emptySlice : Slice := mkSliceFromBits (natToBits 0 0)

private def presentSimpleInput : Slice := mkSliceWithBitsRefs (natToBits 1 1) #[valueCellA]
private def presentSimpleRemainder : Slice := emptySlice
private def presentSimplePushOut : Array Value :=
  #[.cell valueCellA, .slice presentSimpleRemainder]

private def presentSimpleBInput : Slice := mkSliceWithBitsRefs (natToBits 1 1) #[valueCellB]
private def presentSimpleBPushOut : Array Value :=
  #[.cell valueCellB, .slice presentSimpleRemainder]

private def presentExtraRefsInput : Slice := mkSliceWithBitsRefs (natToBits 1 1) #[valueCellA, valueCellB]
private def presentExtraRefsRemainder : Slice := mkSliceWithBitsRefs (natToBits 0 0) #[valueCellB]
private def presentExtraRefsPushOut : Array Value :=
  #[.cell valueCellA, .slice presentExtraRefsRemainder]

private def presentLongInput : Slice := mkSliceWithBitsRefs (natToBits 0b1011 4) #[valueCellA, valueCellC]
private def presentLongRemainder : Slice := mkSliceWithBitsRefs (natToBits 0b011 3) #[valueCellC]
private def presentLongPushOut : Array Value :=
  #[.cell valueCellA, .slice presentLongRemainder]

private def presentMissingRef : Slice := mkSliceFromBits (natToBits 1 1)

private def absentSimpleInput : Slice := mkSliceFromBits (natToBits 0 1)
private def absentSimplePushOut : Array Value :=
  #[.null, .slice absentSimpleInput]

private def absentTailInput : Slice := mkSliceWithBitsRefs (natToBits 0b01101 5) #[valueCellA]
private def absentTailPushOut : Array Value :=
  #[.null, .slice absentTailInput]

private def absentWithRefsInput : Slice := mkSliceWithBitsRefs (natToBits 0b0 1) #[valueCellA, valueCellB]
private def absentWithRefsPushOut : Array Value :=
  #[.null, .slice absentWithRefsInput]

private def absentLongInput : Slice := mkSliceWithBitsRefs (natToBits 0b001010 6) #[valueCellA, valueCellB]
private def absentLongPushOut : Array Value :=
  #[.null, .slice absentLongInput]

private def lddictGas : Int :=
  computeExactGasBudget lddictInstr

private def lddictGasMinusOne : Int :=
  if lddictGas > 0 then lddictGas - 1 else 0

private def lddictGasExact : OracleGasLimits :=
  oracleGasLimitsExact lddictGas

private def lddictGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExact lddictGasMinusOne

private def mkProgramSetGas (n : Int) : Array Instr :=
  #[.pushInt (.num n), .tonEnvOp .setGasLimit, lddictInstr]

private def runLDDICT (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictLddict lddictInstr stack

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictLddict .add (VM.push (intV lddictDispatchSentinel)) stack

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lddictInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lddictId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value := #[])
    (code : Cell)
    (program : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lddictId
    initStack := stack
    codeCell? := some code
    program := program
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeErr
    (label : String)
    (cell : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected error {expected}, got {reprStr actual} ({bits} bits)")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleOk
    (label : String)
    (instr : Instr)
    (expectedBits : BitString) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok c =>
      if c.bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {reprStr expectedBits}, got {reprStr c.bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")

private def expectDecodeOk
    (label : String)
    (cell : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (actual, 16, rest) =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr actual}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected exact decode")
  | .ok (_, bits, _) =>
      throw (IO.userError s!"{label}: expected 16 bits, got {bits}")

private def genLDDICTFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 30
  let (baseCase, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/underflow-empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/type-int" #[intV 7], rng1)
    else if shape = 2 then
      (mkCase "fuzz/type-slice" #[.slice emptySlice, .null], rng1)
    else if shape = 3 then
      (mkCase "fuzz/no-bit" #[.slice emptySlice], rng1)
    else if shape = 4 then
      (mkCase "fuzz/present-missing-ref" #[.slice presentMissingRef], rng1)
    else if shape = 5 then
      (mkCase "fuzz/present-simple-a" #[.slice presentSimpleInput], rng1)
    else if shape = 6 then
      (mkCase "fuzz/present-simple-b" #[.slice presentSimpleBInput], rng1)
    else if shape = 7 then
      (mkCase "fuzz/present-extra-ref" #[.slice presentExtraRefsInput], rng1)
    else if shape = 8 then
      (mkCase "fuzz/present-long" #[.slice presentLongInput], rng1)
    else if shape = 9 then
      (mkCase "fuzz/absent-simple" #[.slice absentSimpleInput], rng1)
    else if shape = 10 then
      (mkCase "fuzz/absent-tail" #[.slice absentTailInput], rng1)
    else if shape = 11 then
      (mkCase "fuzz/absent-with-refs" #[.slice absentWithRefsInput], rng1)
    else if shape = 12 then
      (mkCase "fuzz/absent-long" #[.slice absentLongInput], rng1)
    else if shape = 13 then
      (mkCodeCase "fuzz/decode/f404" #[] rawF404, rng1)
    else if shape = 14 then
      (mkCodeCase "fuzz/decode/f405" #[] rawF405, rng1)
    else if shape = 15 then
      (mkCodeCase "fuzz/decode/f406" #[] rawF406, rng1)
    else if shape = 16 then
      (mkCodeCase "fuzz/decode/f407" #[] rawF407, rng1)
    else if shape = 17 then
      (mkCodeCase "fuzz/decode/f403" #[] rawF403, rng1)
    else if shape = 18 then
      (mkCodeCase "fuzz/decode/f408" #[] rawF408, rng1)
    else if shape = 19 then
      (mkCodeCase "fuzz/decode/truncated-8" #[] rawF4, rng1)
    else if shape = 20 then
      (mkCodeCase "fuzz/decode/truncated-15" #[] raw15Inv, rng1)
    else if shape = 21 then
      (mkCodeCase "fuzz/gas/exact/present"
        #[] rawF404 (mkProgramSetGas lddictGas) lddictGasExact, rng1)
    else if shape = 22 then
      (mkCase "fuzz/gas/minus-one/present"
        #[.slice presentSimpleInput] (mkProgramSetGas lddictGasMinusOne) lddictGasExactMinusOne, rng1)
    else if shape = 23 then
      (mkCase "fuzz/gas/exact/absent"
        #[.slice absentSimpleInput] (mkProgramSetGas lddictGas) lddictGasExact, rng1)
    else if shape = 24 then
      (mkCase "fuzz/gas/minus-one/absent"
        #[.slice absentSimpleInput] (mkProgramSetGas lddictGasMinusOne) lddictGasExactMinusOne, rng1)
    else if shape = 25 then
      (mkCase "fuzz/type-wrong-a" #[.tuple #[]], rng1)
    else if shape = 26 then
      (mkCase "fuzz/type-wrong-b" #[.builder Builder.empty], rng1)
    else if shape = 27 then
      (mkCase "fuzz/surprise-simple" #[.slice presentSimpleInput], rng1)
    else if shape = 28 then
      (mkCase "fuzz/surprise-absent" #[.slice absentTailInput], rng1)
    else if shape = 29 then
      (mkCase "fuzz/surprise-missing-ref" #[.slice presentMissingRef], rng1)
    else
      (mkCase "fuzz/replay/extra" #[.slice presentExtraRefsInput], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lddictId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runDispatchFallback #[] with
        | .ok stack =>
            if stack != #[intV lddictDispatchSentinel] then
              throw (IO.userError s!"dispatch fallback: expected {[intV lddictDispatchSentinel]}, got {reprStr stack}")
        | .error e =>
            throw (IO.userError s!"dispatch fallback: expected success, got {e}") },
    { name := "unit/runtime/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runLDDICT #[]) .stkUnd },
    { name := "unit/runtime/type-error" -- [B2]
      run := do
        expectErr "type-check" (runLDDICT #[intV 17]) .typeChk },
    { name := "unit/runtime/no-bit" -- [B3]
      run := do
        expectErr "no-bit" (runLDDICT #[.slice emptySlice]) .cellUnd },
    { name := "unit/runtime/present-missing-ref" -- [B3]
      run := do
        expectErr "present-missing-ref" (runLDDICT #[.slice presentMissingRef]) .cellUnd },
    { name := "unit/runtime/present-simple" -- [B5][B6]
      run := do
        expectOkStack "present-simple" (runLDDICT #[.slice presentSimpleInput]) presentSimplePushOut },
    { name := "unit/runtime/present-simple-b" -- [B5][B6]
      run := do
        expectOkStack "present-simple-b" (runLDDICT #[.slice presentSimpleBInput]) presentSimpleBPushOut },
    { name := "unit/runtime/present-extra-refs" -- [B5][B6]
      run := do
        expectOkStack "present-extra-refs" (runLDDICT #[.slice presentExtraRefsInput]) presentExtraRefsPushOut },
    { name := "unit/runtime/present-long" -- [B5][B6]
      run := do
        expectOkStack "present-long" (runLDDICT #[.slice presentLongInput]) presentLongPushOut },
    { name := "unit/runtime/absent-simple" -- [B4][B6]
      run := do
        expectOkStack "absent-simple" (runLDDICT #[.slice absentSimpleInput]) absentSimplePushOut },
    { name := "unit/runtime/absent-tail" -- [B4][B6]
      run := do
        expectOkStack "absent-tail" (runLDDICT #[.slice absentTailInput]) absentTailPushOut },
    { name := "unit/runtime/absent-with-refs" -- [B4][B6]
      run := do
        expectOkStack "absent-with-refs" (runLDDICT #[.slice absentWithRefsInput]) absentWithRefsPushOut },
    { name := "unit/runtime/absent-long-with-refs" -- [B4][B6]
      run := do
        expectOkStack "absent-long-with-refs" (runLDDICT #[.slice absentLongInput]) absentLongPushOut },
    { name := "unit/decode/lddict" -- [B7]
      run := do
        expectDecodeOk "decode/f404" rawF404 (.lddict false false) },
    { name := "unit/decode/lddict-variants" -- [B7]
      run := do
        expectDecodeOk "decode/f405" rawF405 (.lddict true false)
        expectDecodeOk "decode/f406" rawF406 (.lddict false true)
        expectDecodeOk "decode/f407" rawF407 (.lddict true true) },
    { name := "unit/decode/adjacent-opcodes" -- [B7]
      run := do
        expectDecodeOk "decode/f403" rawF403 (.dictExt (.lddicts false))  },
    { name := "unit/decode/truncated" -- [B7]
      run := do
        expectDecodeErr "decode/truncated-8" rawF4 .invOpcode
        expectDecodeErr "decode/truncated-15" raw15Inv .invOpcode
        expectDecodeErr "decode/f408-invalid" rawF408 .invOpcode },
    { name := "unit/asm/variants" -- [B8]
      run := do
        expectAssembleOk "asm/lddict" (.lddict false false) (natToBits 0xf404 16)
        expectAssembleOk "asm/lddict-preload" (.lddict true false) (natToBits 0xf405 16)
        expectAssembleOk "asm/lddictq" (.lddict false true) (natToBits 0xf406 16)
        expectAssembleOk "asm/lddictq-preload" (.lddict true true) (natToBits 0xf407 16) }
  ]
  oracle := #[
    mkCase "oracle/underflow-empty" #[], -- [B2]
    mkCase "oracle/type-int" #[intV 7], -- [B2]
    mkCase "oracle/type-slice" #[.slice emptySlice, .null], -- [B2]
    mkCase "oracle/type-builder" #[.builder Builder.empty], -- [B2]
    mkCase "oracle/type-tuple" #[.tuple #[]], -- [B2]
    mkCase "oracle/no-bit" #[.slice emptySlice], -- [B3]
    mkCase "oracle/present-missing-ref" #[.slice presentMissingRef], -- [B3]
    mkCase "oracle/present-simple-a" #[.slice presentSimpleInput], -- [B5][B6]
    mkCase "oracle/present-simple-b" #[.slice presentSimpleBInput], -- [B5][B6]
    mkCase "oracle/present-extra-refs" #[.slice presentExtraRefsInput], -- [B5][B6]
    mkCase "oracle/present-long" #[.slice presentLongInput], -- [B5][B6]
    mkCase "oracle/absent-simple" #[.slice absentSimpleInput], -- [B4][B6]
    mkCase "oracle/absent-tail" #[.slice absentTailInput], -- [B4][B6]
    mkCase "oracle/absent-long" #[.slice absentLongInput], -- [B4][B6]
    mkCase "oracle/absent-with-refs" #[.slice absentWithRefsInput], -- [B4][B6]
    mkCodeCase "oracle/decode/f404" #[] rawF404, -- [B7]
    mkCodeCase "oracle/decode/f405" #[] rawF405, -- [B7]
    mkCodeCase "oracle/decode/f406" #[] rawF406, -- [B7]
    mkCodeCase "oracle/decode/f407" #[] rawF407, -- [B7]
    mkCodeCase "oracle/decode/f403" #[] rawF403, -- [B7]
    mkCodeCase "oracle/decode/f408" #[] rawF408, -- [B7]
    mkCodeCase "oracle/decode/truncated-8" #[] rawF4, -- [B7]
    mkCodeCase "oracle/decode/truncated-15" #[] raw15Inv, -- [B7]
    mkCase "oracle/gas/exact-present" #[.slice presentSimpleInput] (mkProgramSetGas lddictGas) lddictGasExact, -- [B9]
    mkCase "oracle/gas/minus-one-present" #[.slice presentSimpleInput] (mkProgramSetGas lddictGasMinusOne) lddictGasExactMinusOne, -- [B9]
    mkCase "oracle/gas/exact-absent" #[.slice absentSimpleInput] (mkProgramSetGas lddictGas) lddictGasExact, -- [B9]
    mkCase "oracle/gas/minus-one-absent" #[.slice absentSimpleInput] (mkProgramSetGas lddictGasMinusOne) lddictGasExactMinusOne, -- [B9]
    mkCase "oracle/surprise/present-simple-a" #[.slice presentSimpleInput], -- [B5]
    mkCase "oracle/surprise/absent-simple" #[.slice absentSimpleInput], -- [B4]
    mkCase "oracle/surprise/missing-ref" #[.slice presentMissingRef], -- [B3]
    mkCase "oracle/surprise/type-int" #[intV 99], -- [B2]
    mkCase "oracle/replay-extra-1" #[.slice presentSimpleBInput] -- [B5]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr lddictId
      count := 500
      gen := genLDDICTFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.LDDICT
