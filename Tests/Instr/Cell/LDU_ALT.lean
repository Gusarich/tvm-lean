import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDU_ALT

/-
LDU_ALT branch-mapping notes (fixed-width unsigned load alias, non-prefetch, non-quiet):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadInt.lean`
    (`.loadInt true false false bits`)
  - `TvmLean/Semantics/Exec/Cell/Ldu.lean`
    (`.ldu bits`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (short `0xd3xx` + fixed2 `0xd708>>3` decode family)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.ldu` encodes; fixed `.loadInt _ _ _ _` currently rejects with `.invOpcode`)
- C++ authority:
  - `~/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_int_fixed`, `exec_load_int_fixed2`, `exec_load_int_common`, mode=`1`).

Alias contract used in this suite:
- `LDU_ALT` corresponds to the fixed2 decode branch `0xd708>>3` with flags=`001`,
  i.e. `.loadInt true false false bits`;
- canonical short `LDU` (`0xd3xx`) executes the same C++ common path
  (`exec_load_int_common(..., mode=1)`).

Assembler gap + proxy pattern:
- Lean decoder recognizes fixed2 LDU_ALT words, but assembler cannot emit
  `.loadInt true false false bits` today.
- Oracle/fuzz therefore execute a proxy program (`.ldu bits`), while direct unit
  tests still validate the fixed2 alias handler and raw fixed2 decode.

Oracle harness constraint:
- oracle token encoding supports full-cell slices only (`bitPos = 0`, `refPos = 0`);
  oracle/fuzz cases in this suite use only full-cell slices.
-/

private def lduAltId : InstrId := { name := "LDU_ALT" }

private def dispatchSentinel : Int := 969

private def lduAltInstr (bits : Nat) : Instr :=
  .loadInt true false false bits

private def lduProxyInstr (bits : Nat) : Instr :=
  .ldu bits

private def loadIntFixedWord (unsigned prefetch quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat :=
    (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := (0xd708 >>> 3)
  (prefix13 <<< 11) + args11

private def lduAltWord (bits : Nat) : Nat :=
  loadIntFixedWord true false false bits

private def lduShortWord (bits : Nat) : Nat :=
  0xd300 + (bits - 1)

private def ldiShortWord (bits : Nat) : Nat :=
  0xd200 + (bits - 1)

private def mkLduAltCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[lduProxyInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lduAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLduAltDirect (bits : Nat) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt (lduAltInstr bits) stack

private def runLduProxyDirect (bits : Nat) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLdu (lduProxyInstr bits) stack

private def runLduAltDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadInt instr (VM.push (intV dispatchSentinel)) stack

private def expectSameOutcome
    (label : String)
    (aliasRes proxyRes : Except Excno (Array Value)) : IO Unit := do
  let same :=
    match aliasRes, proxyRes with
    | .ok av, .ok pv => av == pv
    | .error ae, .error pe => ae == pe
    | _, _ => false
  if same then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected identical outcomes, got alias={reprStr aliasRes}, proxy={reprStr proxyRes}")

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkLduAltInput
    (bits : Nat)
    (tail : BitString := #[])
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase ++ tail) refs

private def mkLduAltWordInput
    (bits word : Nat)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (natToBits word bits ++ tail) refs

private def expectedUnsigned (slice : Slice) (bits : Nat) : Int :=
  Int.ofNat (bitsToNat (slice.readBits bits))

private def tailBits3 : BitString := natToBits 5 3
private def tailBits5 : BitString := natToBits 21 5
private def tailBits7 : BitString := natToBits 93 7
private def tailBits11 : BitString := natToBits 1337 11
private def tailBits13 : BitString := natToBits 4242 13

private def refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
private def refLeafB : Cell := Cell.mkOrdinary (natToBits 9 4) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 3 2) #[]

private def lduAltGasProbeBits : Nat := 8

private def lduAltProxySetGasExact : Int :=
  computeExactGasBudget (lduProxyInstr lduAltGasProbeBits)

private def lduAltProxySetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (lduProxyInstr lduAltGasProbeBits)

private def lduAltBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickLduAltBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (lduAltBitsBoundaryPool.size - 1)
  (lduAltBitsBoundaryPool[idx]!, rng')

private def pickLduAltBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickLduAltBitsBoundary rng1
  else
    randNat rng1 1 256

private def pickRefPack (rng : StdGen) : Array Cell × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let refs :=
    if pick = 0 then #[refLeafA]
    else if pick = 1 then #[refLeafA, refLeafB]
    else #[refLeafA, refLeafB, refLeafC]
  (refs, rng')

private def pickNoise (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 3
  let value : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 77
    else if pick = 2 then .cell Cell.empty
    else .builder Builder.empty
  (value, rng')

private def genLduAltFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (bits, rng2) := pickLduAltBitsMixed rng1
  let (phase, rng3) := randNat rng2 0 1
  if shape = 0 then
    (mkLduAltCase s!"fuzz/ok/exact/bits-{bits}" bits
      #[.slice (mkLduAltInput bits #[] phase)], rng3)
  else if shape = 1 then
    let (tailLen, rng4) := randNat rng3 1 24
    let tail := stripeBits tailLen (phase + 1)
    (mkLduAltCase s!"fuzz/ok/tail/bits-{bits}/tail-{tailLen}" bits
      #[.slice (mkLduAltInput bits tail phase)], rng4)
  else if shape = 2 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (refs, rng5) := pickRefPack rng4
    (mkLduAltCase s!"fuzz/ok/refs/bits-{bits}/tail-{tailLen}/refs-{refs.size}" bits
      #[.slice (mkLduAltInput bits tail phase refs)], rng5)
  else if shape = 3 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (noise, rng5) := pickNoise rng4
    (mkLduAltCase s!"fuzz/ok/deep/bits-{bits}/tail-{tailLen}" bits
      #[noise, .slice (mkLduAltInput bits tail phase)], rng5)
  else if shape = 4 then
    let available := bits - 1
    (mkLduAltCase s!"fuzz/cellund/by1/bits-{bits}/avail-{available}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits available phase))], rng3)
  else if shape = 5 then
    let maxDelta := Nat.min bits 8
    let (delta, rng4) := randNat rng3 1 maxDelta
    let available := bits - delta
    let (refs, rng5) := pickRefPack rng4
    (mkLduAltCase s!"fuzz/cellund/delta-{delta}/bits-{bits}/avail-{available}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits available phase) refs)], rng5)
  else if shape = 6 then
    (mkLduAltCase s!"fuzz/cellund/empty-slice/bits-{bits}" bits #[.slice (mkSliceFromBits #[])], rng3)
  else if shape = 7 then
    let (refs, rng4) := pickRefPack rng3
    (mkLduAltCase s!"fuzz/cellund/refs-only/bits-{bits}/refs-{refs.size}" bits
      #[.slice (mkSliceWithBitsRefs #[] refs)], rng4)
  else if shape = 8 then
    (mkLduAltCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng3)
  else if shape = 9 then
    (mkLduAltCase s!"fuzz/type/top-null/bits-{bits}" bits #[.null], rng3)
  else if shape = 10 then
    (mkLduAltCase s!"fuzz/type/top-int/bits-{bits}" bits #[intV 0], rng3)
  else if shape = 11 then
    (mkLduAltCase s!"fuzz/type/top-cell/bits-{bits}" bits #[.cell Cell.empty], rng3)
  else if shape = 12 then
    (mkLduAltCase s!"fuzz/type/top-builder/bits-{bits}" bits #[.builder Builder.empty], rng3)
  else if shape = 13 then
    (mkLduAltCase s!"fuzz/type/deep-top-not-slice/bits-{bits}" bits
      #[.slice (mkLduAltInput bits tailBits3 phase), .null], rng3)
  else if shape = 14 then
    (mkLduAltCase "fuzz/ok/min-boundary" 1 #[.slice (mkLduAltWordInput 1 1 tailBits3)], rng3)
  else if shape = 15 then
    (mkLduAltCase "fuzz/ok/max-boundary" 256 #[.slice (mkLduAltInput 256 tailBits5 0)], rng3)
  else if shape = 16 then
    (mkLduAltCase "fuzz/cellund/max-by1" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))], rng3)
  else if shape = 17 then
    (mkLduAltCase s!"fuzz/type/order-top-not-slice-over-short-slice/bits-{bits}" bits
      #[.slice (mkSliceWithBitsRefs #[]), .null], rng3)
  else
    let (useExact, rng4) := randBool rng3
    if useExact then
      (mkLduAltCase "fuzz/gas/exact" lduAltGasProbeBits
        #[.slice (mkLduAltInput lduAltGasProbeBits tailBits11 phase)]
        #[.pushInt (.num lduAltProxySetGasExact), .tonEnvOp .setGasLimit,
          lduProxyInstr lduAltGasProbeBits],
        rng4)
    else
      (mkLduAltCase "fuzz/gas/exact-minus-one" lduAltGasProbeBits
        #[.slice (mkLduAltInput lduAltGasProbeBits tailBits11 phase)]
        #[.pushInt (.num lduAltProxySetGasExactMinusOne), .tonEnvOp .setGasLimit,
          lduProxyInstr lduAltGasProbeBits],
        rng4)

def suite : InstrSuite where
  id := lduAltId
  unit := #[
    { name := "unit/direct/alias-success-pushes-unsigned-int-then-remainder"
      run := do
        let checks : Array (Nat × Slice) :=
          #[
            (1, mkLduAltWordInput 1 0),
            (1, mkLduAltWordInput 1 1 tailBits7),
            (2, mkLduAltWordInput 2 3 tailBits3),
            (8, mkLduAltWordInput 8 0 tailBits5),
            (8, mkLduAltWordInput 8 0xff),
            (16, mkLduAltWordInput 16 0xface tailBits7),
            (255, mkLduAltInput 255 #[] 0),
            (255, mkLduAltInput 255 #[true] 1),
            (256, mkLduAltInput 256 #[] 1),
            (256, mkLduAltInput 256 tailBits3 0)
          ]
        for (bits, input) in checks do
          expectOkStack s!"ok/bits-{bits}/len-{input.bitsRemaining}"
            (runLduAltDirect bits #[.slice input])
            #[intV (expectedUnsigned input bits), .slice (input.advanceBits bits)]

        let refsInput := mkLduAltWordInput 8 0xa5 tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-preserved-in-remainder"
          (runLduAltDirect 8 #[.slice refsInput])
          #[intV (expectedUnsigned refsInput 8), .slice (refsInput.advanceBits 8)]

        let deepInput := mkLduAltWordInput 16 0x1234 tailBits7
        expectOkStack "ok/deep-stack-preserved"
          (runLduAltDirect 16 #[.null, intV 99, .slice deepInput])
          #[.null, intV 99, intV (expectedUnsigned deepInput 16), .slice (deepInput.advanceBits 16)] }
    ,
    { name := "unit/direct/alias-cellund-insufficient-bits"
      run := do
        let insuff : Array (Nat × Nat) :=
          #[
            (1, 0),
            (8, 7),
            (64, 63),
            (255, 254),
            (256, 255)
          ]
        for (bits, available) in insuff do
          let slice := mkSliceWithBitsRefs (stripeBits available 0)
          expectErr s!"cellund/bits-{bits}/avail-{available}"
            (runLduAltDirect bits #[.slice slice]) .cellUnd

        let refsOnly := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]
        expectErr "cellund/refs-only-no-bits"
          (runLduAltDirect 8 #[.slice refsOnly]) .cellUnd }
    ,
    { name := "unit/direct/alias-range-underflow-type-and-ordering"
      run := do
        expectErr "range/bits0-empty-stack"
          (runLduAltDirect 0 #[]) .rangeChk
        expectErr "range/bits0-top-not-slice"
          (runLduAltDirect 0 #[.null]) .rangeChk
        expectErr "range/bits0-valid-slice"
          (runLduAltDirect 0 #[.slice (mkLduAltInput 1 #[] 0)]) .rangeChk

        expectErr "underflow/empty"
          (runLduAltDirect 8 #[]) .stkUnd
        expectErr "type/top-null"
          (runLduAltDirect 8 #[.null]) .typeChk
        expectErr "type/top-int"
          (runLduAltDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell"
          (runLduAltDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder"
          (runLduAltDirect 8 #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLduAltDirect 8 #[.slice (mkLduAltInput 8 tailBits3 0), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runLduAltDirect 8 #[.slice (mkSliceWithBitsRefs #[]), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-boundaries-and-assembler-gap"
      run := do
        let asmProgram : Array Instr :=
          #[lduProxyInstr 1, lduProxyInstr 8, lduProxyInstr 255, lduProxyInstr 256, .add]
        let asmCode ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/short-seq failed: {e}")
        let a0 := Slice.ofCell asmCode
        let a1 ← expectDecodeStep "decode/asm-short-1" a0 (lduProxyInstr 1) 16
        let a2 ← expectDecodeStep "decode/asm-short-8" a1 (lduProxyInstr 8) 16
        let a3 ← expectDecodeStep "decode/asm-short-255" a2 (lduProxyInstr 255) 16
        let a4 ← expectDecodeStep "decode/asm-short-256" a3 (lduProxyInstr 256) 16
        let a5 ← expectDecodeStep "decode/asm-short-tail-add" a4 .add 8
        if a5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-short-end: expected exhausted slice, got {a5.bitsRemaining} bits remaining")

        let asm8 ←
          match assembleCp0 [lduProxyInstr 8] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/ldu-8 failed: {e}")
        if asm8.bits = natToBits (lduShortWord 8) 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/ldu-8: expected short 16-bit encoding, got {asm8.bits}")
        if asm8.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/ldu-8: expected 16 bits, got {asm8.bits.size}")

        match assembleCp0 [lduProxyInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/ldu-0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/ldu-0: expected rangeChk, got success")

        match assembleCp0 [lduProxyInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/ldu-257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/ldu-257: expected rangeChk, got success")

        match assembleCp0 [lduAltInstr 1] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/alt-1: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/alt-1: expected invOpcode, got success")

        match assembleCp0 [lduAltInstr 256] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/alt-256: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/alt-256: expected invOpcode, got success")

        match assembleCp0 [lduAltInstr 0] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/alt-0: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/alt-0: expected invOpcode, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")

        let shortRawBits : BitString :=
          natToBits (ldiShortWord 8) 16
            ++ natToBits (lduShortWord 8) 16
            ++ natToBits 0xd4 8
            ++ addCell.bits
        let s0 := mkSliceFromBits shortRawBits
        let s1 ← expectDecodeStep "decode/raw-ldi-8-neighbor" s0 (.loadInt false false false 8) 16
        let s2 ← expectDecodeStep "decode/raw-ldu-8-short" s1 (lduProxyInstr 8) 16
        let s3 ← expectDecodeStep "decode/raw-ldref-neighbor" s2 .ldref 8
        let s4 ← expectDecodeStep "decode/raw-short-tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-short-end: expected exhausted slice, got {s4.bitsRemaining} bits remaining")

        let fixedRawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd707 16 ++
             natToBits (lduAltWord 1) 24 ++
             natToBits (loadIntFixedWord false false false 8) 24 ++
             natToBits (lduAltWord 256) 24 ++
             natToBits 0xd710 16 ++
             addCell.bits) #[]
        let f0 := Slice.ofCell fixedRawCode
        let f1 ← expectDecodeStep "decode/raw-boundary-plduxq" f0 (.loadIntVar true true true) 16
        let f2 ← expectDecodeStep "decode/raw-alt-ldu-1" f1 (lduAltInstr 1) 24
        let f3 ← expectDecodeStep "decode/raw-fixed-ldi-8-neighbor" f2 (.loadInt false false false 8) 24
        let f4 ← expectDecodeStep "decode/raw-alt-ldu-256" f3 (lduAltInstr 256) 24
        let f5 ← expectDecodeStep "decode/raw-boundary-plduz-0" f4 (.cellExt (.plduz 0)) 16
        let f6 ← expectDecodeStep "decode/raw-fixed-tail-add" f5 .add 8
        if f6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-fixed-end: expected exhausted slice, got {f6.bitsRemaining} bits remaining") }
    ,
    { name := "unit/alias-equivalence/fixed2-vs-short-ldu"
      run := do
        let okChecks : Array (Nat × Slice) :=
          #[
            (1, mkLduAltWordInput 1 1 tailBits3),
            (8, mkLduAltWordInput 8 0xa5 tailBits5),
            (32, mkLduAltInput 32 tailBits7 0),
            (256, mkLduAltInput 256 tailBits3 1)
          ]
        for (bits, input) in okChecks do
          expectSameOutcome s!"align/ok/bits-{bits}"
            (runLduAltDirect bits #[.slice input])
            (runLduProxyDirect bits #[.slice input])

        let insuff : Array (Nat × Nat) := #[(1, 0), (8, 7), (256, 255)]
        for (bits, available) in insuff do
          let slice := mkSliceWithBitsRefs (stripeBits available 0)
          expectSameOutcome s!"align/cellund/bits-{bits}/avail-{available}"
            (runLduAltDirect bits #[.slice slice])
            (runLduProxyDirect bits #[.slice slice])

        expectSameOutcome "align/underflow-empty"
          (runLduAltDirect 8 #[])
          (runLduProxyDirect 8 #[])
        expectSameOutcome "align/type-top-null"
          (runLduAltDirect 8 #[.null])
          (runLduProxyDirect 8 #[.null])
        expectSameOutcome "align/range-bits0-before-pop"
          (runLduAltDirect 0 #[.slice (mkLduAltInput 8 #[] 0)])
          (runLduProxyDirect 0 #[.slice (mkLduAltInput 8 #[] 0)])

        let mappingBits : Array Nat := #[1, 8, 255, 256]
        for bits in mappingBits do
          let altSlice := mkSliceFromBits (natToBits (lduAltWord bits) 24)
          let shortSlice := mkSliceFromBits (natToBits (lduShortWord bits) 16)

          let decodedAlt ←
            match decodeCp0WithBits altSlice with
            | .ok (instr, used, _) =>
                if used = 24 then
                  pure instr
                else
                  throw (IO.userError s!"decode/map/alt/bits-{bits}: expected 24-bit decode, got {used}")
            | .error e =>
                throw (IO.userError s!"decode/map/alt/bits-{bits}: failed with {e}")
          let decodedShort ←
            match decodeCp0WithBits shortSlice with
            | .ok (instr, used, _) =>
                if used = 16 then
                  pure instr
                else
                  throw (IO.userError s!"decode/map/short/bits-{bits}: expected 16-bit decode, got {used}")
            | .error e =>
                throw (IO.userError s!"decode/map/short/bits-{bits}: failed with {e}")

          if decodedAlt == lduAltInstr bits then
            pure ()
          else
            throw (IO.userError s!"decode/map/alt/bits-{bits}: unexpected instruction {reprStr decodedAlt}")
          if decodedShort == lduProxyInstr bits then
            pure ()
          else
            throw (IO.userError s!"decode/map/short/bits-{bits}: unexpected instruction {reprStr decodedShort}")

          let input := mkLduAltInput bits tailBits7 (bits % 2) #[refLeafA]
          expectSameOutcome s!"align/decoded/bits-{bits}"
            (runHandlerDirect execInstrCellLoadInt decodedAlt #[.slice input])
            (runHandlerDirect execInstrCellLdu decodedShort #[.slice input]) }
    ,
    { name := "unit/dispatch/non-loadint-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runLduAltDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/short-ldu-neighbor"
          (runLduAltDispatchFallback (lduProxyInstr 8) #[intV 11])
          #[intV 11, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-cell-op"
          (runLduAltDispatchFallback .ldref #[.cell Cell.empty])
          #[.cell Cell.empty, intV dispatchSentinel] }
  ]
  oracle := #[
    mkLduAltCase "ok/bits-1/exact-zero" 1 #[.slice (mkLduAltWordInput 1 0)],
    mkLduAltCase "ok/bits-1/tail7-one" 1 #[.slice (mkLduAltWordInput 1 1 tailBits7)],
    mkLduAltCase "ok/bits-2/tail5-max" 2 #[.slice (mkLduAltWordInput 2 3 tailBits5)],
    mkLduAltCase "ok/bits-3/tail11" 3 #[.slice (mkLduAltInput 3 tailBits11 1)],
    mkLduAltCase "ok/bits-7/tail13" 7 #[.slice (mkLduAltInput 7 tailBits13 0)],
    mkLduAltCase "ok/bits-8/exact-max" 8 #[.slice (mkLduAltWordInput 8 0xff)],
    mkLduAltCase "ok/bits-8/tail11-zero" 8 #[.slice (mkLduAltWordInput 8 0 tailBits11)],
    mkLduAltCase "ok/bits-15/exact" 15 #[.slice (mkLduAltInput 15 #[] 1)],
    mkLduAltCase "ok/bits-16/tail7-word" 16 #[.slice (mkLduAltWordInput 16 0x1234 tailBits7)],
    mkLduAltCase "ok/bits-31/exact" 31 #[.slice (mkLduAltInput 31 #[] 0)],
    mkLduAltCase "ok/bits-63/tail5" 63 #[.slice (mkLduAltInput 63 tailBits5 1)],
    mkLduAltCase "ok/bits-127/exact" 127 #[.slice (mkLduAltInput 127 #[] 1)],
    mkLduAltCase "ok/bits-255/exact" 255 #[.slice (mkLduAltInput 255 #[] 0)],
    mkLduAltCase "ok/bits-255/tail1" 255 #[.slice (mkLduAltInput 255 #[true] 1)],
    mkLduAltCase "ok/bits-256/exact" 256 #[.slice (mkLduAltInput 256 #[] 0)],
    mkLduAltCase "ok/bits-256/tail3" 256 #[.slice (mkLduAltInput 256 tailBits3 1)],
    mkLduAltCase "ok/bits-8/refs2" 8 #[.slice (mkLduAltWordInput 8 0xa5 tailBits5 #[refLeafA, refLeafB])],
    mkLduAltCase "ok/bits-32/refs3-tail7" 32
      #[.slice (mkLduAltInput 32 tailBits7 1 #[refLeafA, refLeafB, refLeafC])],
    mkLduAltCase "ok/deep-stack-preserve" 8
      #[.null, intV 42, .slice (mkLduAltInput 8 tailBits7 1)],
    mkLduAltCase "ok/deep-stack-with-refs" 32
      #[.cell Cell.empty, .slice (mkLduAltInput 32 tailBits5 0 #[refLeafA])],

    mkLduAltCase "cellund/bits-1/avail0" 1 #[.slice (mkSliceWithBitsRefs #[])],
    mkLduAltCase "cellund/bits-8/avail7" 8 #[.slice (mkSliceWithBitsRefs (stripeBits 7 0))],
    mkLduAltCase "cellund/bits-64/avail63" 64 #[.slice (mkSliceWithBitsRefs (stripeBits 63 1))],
    mkLduAltCase "cellund/bits-255/avail254" 255 #[.slice (mkSliceWithBitsRefs (stripeBits 254 0))],
    mkLduAltCase "cellund/bits-256/avail255" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))],
    mkLduAltCase "cellund/bits-32/avail0-refs2" 32
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkLduAltCase "cellund/refs-only-no-bits" 8
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA])],

    mkLduAltCase "underflow/empty" 8 #[],
    mkLduAltCase "type/top-null" 8 #[.null],
    mkLduAltCase "type/top-int" 8 #[intV 0],
    mkLduAltCase "type/top-cell" 8 #[.cell Cell.empty],
    mkLduAltCase "type/top-builder" 8 #[.builder Builder.empty],
    mkLduAltCase "type/deep-top-not-slice" 8 #[.slice (mkLduAltInput 8 tailBits3 0), .null],
    mkLduAltCase "type/order-top-not-slice-over-short-slice" 8 #[.slice (mkSliceWithBitsRefs #[]), .null],

    mkLduAltCase "gas/exact-cost-succeeds" lduAltGasProbeBits
      #[.slice (mkLduAltInput lduAltGasProbeBits tailBits11 1)]
      #[.pushInt (.num lduAltProxySetGasExact), .tonEnvOp .setGasLimit, lduProxyInstr lduAltGasProbeBits],
    mkLduAltCase "gas/exact-minus-one-out-of-gas" lduAltGasProbeBits
      #[.slice (mkLduAltInput lduAltGasProbeBits tailBits11 1)]
      #[.pushInt (.num lduAltProxySetGasExactMinusOne), .tonEnvOp .setGasLimit,
        lduProxyInstr lduAltGasProbeBits]
  ]
  fuzz := #[
    { seed := 2026021103
      count := 320
      gen := genLduAltFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDU_ALT
