import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDI_ALT

/-
LDI_ALT alias branch-mapping notes (fixed-width alt form, non-prefetch, signed, non-quiet):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadInt.lean`
    (`.loadInt false false false bits`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xd2xx` short LDI and `0xd708>>3` fixed-width load-int decode families)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.loadInt _ _ _ _` currently rejects assembly with `.invOpcode`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_int_fixed`, `exec_load_int_fixed2`, `exec_load_int_common`, mode=`0`).

Alias contract covered by this suite:
- canonical short LDI (`0xd2xx`, 16-bit) and LDI_ALT (`0xd708>>3` + args11, 24-bit)
  both decode to `.loadInt false false false bits` and execute via the same
  C++ common path (`exec_load_int_common`, mode 0).

Branch map used for this suite (`LDI_ALT` semantics):
- bits==0 guard: immediate `rangeChk` before any stack read;
- stack underflow/type from `popSlice` when bits>0;
- success (`have(bits)`): push signed integer then remainder slice;
- failure (`!have(bits)`): throw `cellUnd` (non-quiet);
- handler dispatch fallthrough for non-`.loadInt` instructions.

Assembler/proxy note:
- LDI/LDI_ALT are pure decode aliases in Lean today (`.loadInt` assemble is `.invOpcode`),
  so oracle/fuzz use executable proxy `LDIX` (`.loadIntVar false false false`) with an
  explicit `bits` value on stack.
- Unit tests keep direct `.loadInt` handler checks plus short-vs-alt decode equivalence.
- Oracle/fuzz slice inputs are full-cell slices (bitPos=0, refPos=0) for compatibility.
-/

private def ldiAltId : InstrId := { name := "LDI_ALT" }

private def dispatchSentinel : Int := 971

private def ldiAltInstr (bits : Nat) : Instr :=
  .loadInt false false false bits

private def ldixInstr : Instr :=
  .loadIntVar false false false

private def ldiAltProxyGasInstr : Instr :=
  ldixInstr

private def loadIntFixedWord (unsigned prefetch quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat :=
    (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := (0xd708 >>> 3)
  (prefix13 <<< 11) + args11

private def ldiAltWord (bits : Nat) : Nat :=
  loadIntFixedWord false false false bits

private def ldiShortWord (bits : Nat) : Nat :=
  0xd200 + (bits - 1)

private def lduShortWord (bits : Nat) : Nat :=
  0xd300 + (bits - 1)

private def mkLdiAltCase
    (name : String)
    (bits : Nat)
    (stackNoBits : Array Value)
    (program : Array Instr := #[ldixInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldiAltId
    program := program
    initStack := stackNoBits.push (intV bits)
    gasLimits := gasLimits
    fuel := fuel }

private def mkLdiAltRawCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldixInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldiAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdiAltDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt (ldiAltInstr bits) stack

private def runLdixDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadIntVar ldixInstr stack

private def runLdiAltDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadInt instr (VM.push (intV dispatchSentinel)) stack

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

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkLdiAltInput
    (bits : Nat)
    (tail : BitString := #[])
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase ++ tail) refs

private def mkLdiAltWordInput
    (bits word : Nat)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (natToBits word bits ++ tail) refs

private def expectedSigned (slice : Slice) (bits : Nat) : Int :=
  bitsToIntSignedTwos (slice.readBits bits)

private def tailBits3 : BitString := natToBits 5 3
private def tailBits5 : BitString := natToBits 21 5
private def tailBits7 : BitString := natToBits 93 7
private def tailBits11 : BitString := natToBits 1337 11
private def tailBits13 : BitString := natToBits 4242 13

private def refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
private def refLeafB : Cell := Cell.mkOrdinary (natToBits 9 4) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 3 2) #[]

private def partialCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 40 0) #[refLeafA, refLeafB]

private def partialCursorSlice : Slice :=
  { cell := partialCursorCell, bitPos := 7, refPos := 1 }

private def shortCursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 24 1) #[refLeafC]

private def shortCursorSlice : Slice :=
  { cell := shortCursorCell, bitPos := 20, refPos := 0 }

private def ldiAltGasProbeBits : Nat := 8

private def ldiAltProxySetGasExact : Int :=
  computeExactGasBudget ldiAltProxyGasInstr

private def ldiAltProxySetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldiAltProxyGasInstr

private def ldiAltBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickLdiAltBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (ldiAltBitsBoundaryPool.size - 1)
  (ldiAltBitsBoundaryPool[idx]!, rng')

private def pickLdiAltBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickLdiAltBitsBoundary rng1
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

private def genLdiAltFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 25
  let (bits, rng2) := pickLdiAltBitsMixed rng1
  let (phase, rng3) := randNat rng2 0 1
  if shape = 0 then
    (mkLdiAltCase s!"fuzz/ok/exact/bits-{bits}" bits
      #[.slice (mkLdiAltInput bits #[] phase)], rng3)
  else if shape = 1 then
    let (tailLen, rng4) := randNat rng3 1 24
    let tail := stripeBits tailLen (phase + 1)
    (mkLdiAltCase s!"fuzz/ok/tail/bits-{bits}/tail-{tailLen}" bits
      #[.slice (mkLdiAltInput bits tail phase)], rng4)
  else if shape = 2 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (refs, rng5) := pickRefPack rng4
    (mkLdiAltCase s!"fuzz/ok/refs/bits-{bits}/tail-{tailLen}/refs-{refs.size}" bits
      #[.slice (mkLdiAltInput bits tail phase refs)], rng5)
  else if shape = 3 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (noise, rng5) := pickNoise rng4
    (mkLdiAltCase s!"fuzz/ok/deep/bits-{bits}/tail-{tailLen}" bits
      #[noise, .slice (mkLdiAltInput bits tail phase)], rng5)
  else if shape = 4 then
    let available := bits - 1
    (mkLdiAltCase s!"fuzz/cellund/by1/bits-{bits}/avail-{available}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits available phase))], rng3)
  else if shape = 5 then
    let maxDelta := Nat.min bits 8
    let (delta, rng4) := randNat rng3 1 maxDelta
    let available := bits - delta
    let (refs, rng5) := pickRefPack rng4
    (mkLdiAltCase s!"fuzz/cellund/delta-{delta}/bits-{bits}/avail-{available}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits available phase) refs)], rng5)
  else if shape = 6 then
    (mkLdiAltCase s!"fuzz/cellund/empty-slice/bits-{bits}" bits #[.slice (mkSliceFromBits #[])], rng3)
  else if shape = 7 then
    let (refs, rng4) := pickRefPack rng3
    (mkLdiAltCase s!"fuzz/cellund/refs-only/bits-{bits}/refs-{refs.size}" bits
      #[.slice (mkSliceWithBitsRefs #[] refs)], rng4)
  else if shape = 8 then
    (mkLdiAltRawCase "fuzz/underflow/empty" #[], rng3)
  else if shape = 9 then
    (mkLdiAltRawCase s!"fuzz/underflow/one-item-width-{bits}" #[intV bits], rng3)
  else if shape = 10 then
    (mkLdiAltCase s!"fuzz/type/top-null/bits-{bits}" bits #[.null], rng3)
  else if shape = 11 then
    (mkLdiAltCase s!"fuzz/type/top-int/bits-{bits}" bits #[intV 0], rng3)
  else if shape = 12 then
    (mkLdiAltCase s!"fuzz/type/top-cell/bits-{bits}" bits #[.cell Cell.empty], rng3)
  else if shape = 13 then
    (mkLdiAltCase s!"fuzz/type/top-builder/bits-{bits}" bits #[.builder Builder.empty], rng3)
  else if shape = 14 then
    (mkLdiAltCase s!"fuzz/type/deep-top-not-slice/bits-{bits}" bits
      #[.slice (mkLdiAltInput bits tailBits3 phase), .null], rng3)
  else if shape = 15 then
    (mkLdiAltCase "fuzz/signed/bits1/neg1" 1 #[.slice (mkLdiAltWordInput 1 1 tailBits3)], rng3)
  else if shape = 16 then
    (mkLdiAltCase "fuzz/signed/bits8/max-pos" 8 #[.slice (mkLdiAltWordInput 8 0x7f tailBits5)], rng3)
  else if shape = 17 then
    (mkLdiAltCase "fuzz/signed/bits8/min-neg" 8 #[.slice (mkLdiAltWordInput 8 0x80 tailBits7)], rng3)
  else if shape = 18 then
    (mkLdiAltCase "fuzz/signed/bits16/min-neg" 16 #[.slice (mkLdiAltWordInput 16 0x8000 tailBits3)], rng3)
  else if shape = 19 then
    (mkLdiAltCase "fuzz/ok/max-boundary-neg" 256 #[.slice (mkLdiAltInput 256 tailBits5 1)], rng3)
  else if shape = 20 then
    (mkLdiAltCase "fuzz/cellund/max-by1" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))], rng3)
  else if shape = 21 then
    (mkLdiAltRawCase "fuzz/range/bits-too-large"
      #[.slice (mkLdiAltInput 8 tailBits3 0), intV 258], rng3)
  else if shape = 22 then
    (mkLdiAltRawCase "fuzz/range/bits-negative"
      #[.slice (mkLdiAltInput 8 tailBits5 1), intV (-1)], rng3)
  else if shape = 23 then
    (mkLdiAltRawCase "fuzz/range/bits-nan"
      #[.slice (mkLdiAltInput 8 tailBits7 0)]
      #[.pushInt .nan, ldixInstr], rng3)
  else if shape = 24 then
    (mkLdiAltRawCase "fuzz/gas/exact"
      #[.slice (mkLdiAltWordInput ldiAltGasProbeBits 0x80 tailBits11), intV ldiAltGasProbeBits]
      #[.pushInt (.num ldiAltProxySetGasExact), .tonEnvOp .setGasLimit, ldixInstr], rng3)
  else
    (mkLdiAltRawCase "fuzz/gas/exact-minus-one"
      #[.slice (mkLdiAltWordInput ldiAltGasProbeBits 0x80 tailBits11), intV ldiAltGasProbeBits]
      #[.pushInt (.num ldiAltProxySetGasExactMinusOne), .tonEnvOp .setGasLimit, ldixInstr], rng3)

def suite : InstrSuite where
  id := ldiAltId
  unit := #[
    { name := "unit/direct/success-pushes-signed-int-then-remainder"
      run := do
        let checks : Array (Nat × Slice) :=
          #[
            (1, mkLdiAltWordInput 1 0),
            (1, mkLdiAltWordInput 1 1 tailBits7),
            (2, mkLdiAltWordInput 2 1 tailBits3),
            (2, mkLdiAltWordInput 2 3),
            (8, mkLdiAltWordInput 8 0),
            (8, mkLdiAltWordInput 8 0x7f tailBits5),
            (8, mkLdiAltWordInput 8 0x80),
            (8, mkLdiAltWordInput 8 0xff tailBits11),
            (16, mkLdiAltWordInput 16 0x7fff tailBits3),
            (16, mkLdiAltWordInput 16 0x8000),
            (255, mkLdiAltInput 255 #[] 0),
            (255, mkLdiAltInput 255 #[true] 1),
            (256, mkLdiAltInput 256 #[] 1),
            (256, mkLdiAltInput 256 tailBits3 0)
          ]
        for (bits, input) in checks do
          expectOkStack s!"ok/bits-{bits}/len-{input.bitsRemaining}"
            (runLdiAltDirect bits #[.slice input])
            #[intV (expectedSigned input bits), .slice (input.advanceBits bits)]

        let refsInput := mkLdiAltWordInput 8 0x80 tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-preserved-in-remainder"
          (runLdiAltDirect 8 #[.slice refsInput])
          #[intV (expectedSigned refsInput 8), .slice (refsInput.advanceBits 8)]

        let deepInput := mkLdiAltWordInput 16 0x8001 tailBits7
        expectOkStack "ok/deep-stack-preserved"
          (runLdiAltDirect 16 #[.null, intV 99, .slice deepInput])
          #[.null, intV 99, intV (expectedSigned deepInput 16), .slice (deepInput.advanceBits 16)]

        expectOkStack "ok/partial-slice-cursor"
          (runLdiAltDirect 12 #[.slice partialCursorSlice])
          #[intV (expectedSigned partialCursorSlice 12), .slice (partialCursorSlice.advanceBits 12)] }
    ,
    { name := "unit/direct/cellund-insufficient-bits"
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
            (runLdiAltDirect bits #[.slice slice]) .cellUnd

        let refsOnly := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]
        expectErr "cellund/refs-only-no-bits"
          (runLdiAltDirect 8 #[.slice refsOnly]) .cellUnd

        expectErr "cellund/partial-cursor-bits5-avail4"
          (runLdiAltDirect 5 #[.slice shortCursorSlice]) .cellUnd }
    ,
    { name := "unit/direct/range-underflow-type-and-ordering"
      run := do
        expectErr "range/bits0-empty-stack"
          (runLdiAltDirect 0 #[]) .rangeChk
        expectErr "range/bits0-top-not-slice"
          (runLdiAltDirect 0 #[.null]) .rangeChk
        expectErr "range/bits0-valid-slice"
          (runLdiAltDirect 0 #[.slice (mkLdiAltInput 1 #[] 0)]) .rangeChk

        expectErr "underflow/empty"
          (runLdiAltDirect 8 #[]) .stkUnd
        expectErr "type/top-null"
          (runLdiAltDirect 8 #[.null]) .typeChk
        expectErr "type/top-int"
          (runLdiAltDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell"
          (runLdiAltDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder"
          (runLdiAltDirect 8 #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdiAltDirect 8 #[.slice (mkLdiAltInput 8 tailBits3 0), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runLdiAltDirect 8 #[.slice (mkSliceWithBitsRefs #[]), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-alias-boundaries-and-assembler-gap"
      run := do
        let proxyAsm ←
          match assembleCp0 [ldixInstr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/proxy-seq failed: {e}")
        let p0 := Slice.ofCell proxyAsm
        let p1 ← expectDecodeStep "decode/asm-proxy-ldix" p0 ldixInstr 16
        let p2 ← expectDecodeStep "decode/asm-proxy-tail-add" p1 .add 8
        if p2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-proxy-end: expected exhausted slice, got {p2.bitsRemaining} bits remaining")

        let proxyOnly ←
          match assembleCp0 [ldixInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/proxy-ldix failed: {e}")
        if proxyOnly.bits = natToBits 0xd700 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/proxy-ldix: expected 0xd700 encoding, got {proxyOnly.bits}")

        match assembleCp0 [ldiAltInstr 1] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/ldi-alt-1: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/ldi-alt-1: expected invOpcode, got success")

        match assembleCp0 [ldiAltInstr 256] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/ldi-alt-256: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/ldi-alt-256: expected invOpcode, got success")

        match assembleCp0 [ldiAltInstr 0] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/ldi-alt-0: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/ldi-alt-0: expected invOpcode, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")

        let shortRawBits : BitString :=
          natToBits 0xd1 8
            ++ natToBits (ldiShortWord 1) 16
            ++ natToBits (ldiShortWord 8) 16
            ++ natToBits (ldiShortWord 256) 16
            ++ natToBits (lduShortWord 8) 16
            ++ addCell.bits
        let s0 := mkSliceFromBits shortRawBits
        let s1 ← expectDecodeStep "decode/raw-short-neighbor-ends" s0 .ends 8
        let s2 ← expectDecodeStep "decode/raw-short-ldi-1" s1 (ldiAltInstr 1) 16
        let s3 ← expectDecodeStep "decode/raw-short-ldi-8" s2 (ldiAltInstr 8) 16
        let s4 ← expectDecodeStep "decode/raw-short-ldi-256" s3 (ldiAltInstr 256) 16
        let s5 ← expectDecodeStep "decode/raw-short-ldu-8-neighbor" s4 (.ldu 8) 16
        let s6 ← expectDecodeStep "decode/raw-short-tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-short-end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        let altRawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd707 16 ++
             natToBits (ldiAltWord 1) 24 ++
             natToBits (loadIntFixedWord true false false 8) 24 ++
             natToBits (loadIntFixedWord false true false 8) 24 ++
             natToBits (loadIntFixedWord false false true 8) 24 ++
             natToBits (ldiAltWord 256) 24 ++
             natToBits 0xd710 16 ++
             addCell.bits) #[]
        let a0 := Slice.ofCell altRawCode
        let a1 ← expectDecodeStep "decode/raw-alt-boundary-plduxq" a0 (.loadIntVar true true true) 16
        let a2 ← expectDecodeStep "decode/raw-alt-ldi-1" a1 (ldiAltInstr 1) 24
        let a3 ← expectDecodeStep "decode/raw-alt-ldu-8-neighbor" a2 (.loadInt true false false 8) 24
        let a4 ← expectDecodeStep "decode/raw-alt-pldi-8-neighbor" a3 (.loadInt false true false 8) 24
        let a5 ← expectDecodeStep "decode/raw-alt-ldiq-8-neighbor" a4 (.loadInt false false true 8) 24
        let a6 ← expectDecodeStep "decode/raw-alt-ldi-256" a5 (ldiAltInstr 256) 24
        let a7 ← expectDecodeStep "decode/raw-alt-boundary-plduz-0" a6 (.cellExt (.plduz 0)) 16
        let a8 ← expectDecodeStep "decode/raw-alt-tail-add" a7 .add 8
        if a8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-alt-end: expected exhausted slice, got {a8.bitsRemaining} bits remaining")

        let mixedRawBits : BitString :=
          natToBits (ldiShortWord 8) 16
            ++ natToBits (ldiAltWord 8) 24
            ++ natToBits (ldiShortWord 256) 16
            ++ natToBits (ldiAltWord 1) 24
            ++ addCell.bits
        let m0 := mkSliceFromBits mixedRawBits
        let m1 ← expectDecodeStep "decode/raw-mixed-short-8" m0 (ldiAltInstr 8) 16
        let m2 ← expectDecodeStep "decode/raw-mixed-alt-8" m1 (ldiAltInstr 8) 24
        let m3 ← expectDecodeStep "decode/raw-mixed-short-256" m2 (ldiAltInstr 256) 16
        let m4 ← expectDecodeStep "decode/raw-mixed-alt-1" m3 (ldiAltInstr 1) 24
        let m5 ← expectDecodeStep "decode/raw-mixed-tail-add" m4 .add 8
        if m5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-mixed-end: expected exhausted slice, got {m5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/alias-equivalence/short-vs-alt-decode-and-exec"
      run := do
        let mappingBits : Array Nat := #[1, 2, 8, 31, 127, 256]
        for bits in mappingBits do
          let shortSlice := mkSliceFromBits (natToBits (ldiShortWord bits) 16)
          let altSlice := mkSliceFromBits (natToBits (ldiAltWord bits) 24)

          let decodedShort ←
            match decodeCp0WithBits shortSlice with
            | .ok (instr, used, _) =>
                if used = 16 then
                  pure instr
                else
                  throw (IO.userError s!"decode/map/short/bits-{bits}: expected 16-bit decode, got {used}")
            | .error e =>
                throw (IO.userError s!"decode/map/short/bits-{bits}: failed with {e}")
          let decodedAlt ←
            match decodeCp0WithBits altSlice with
            | .ok (instr, used, _) =>
                if used = 24 then
                  pure instr
                else
                  throw (IO.userError s!"decode/map/alt/bits-{bits}: expected 24-bit decode, got {used}")
            | .error e =>
                throw (IO.userError s!"decode/map/alt/bits-{bits}: failed with {e}")

          if decodedShort == ldiAltInstr bits then
            pure ()
          else
            throw (IO.userError s!"decode/map/short/bits-{bits}: unexpected instruction {reprStr decodedShort}")
          if decodedAlt == ldiAltInstr bits then
            pure ()
          else
            throw (IO.userError s!"decode/map/alt/bits-{bits}: unexpected instruction {reprStr decodedAlt}")
          if decodedShort == decodedAlt then
            pure ()
          else
            throw (IO.userError s!"decode/map/bits-{bits}: short and alt decoded to different instructions")

          let input := mkLdiAltInput bits tailBits7 (bits % 2) #[refLeafA]
          expectSameOutcome s!"alias/ok/bits-{bits}"
            (runHandlerDirect execInstrCellLoadInt decodedShort #[.slice input])
            (runHandlerDirect execInstrCellLoadInt decodedAlt #[.slice input])

          let available := bits - 1
          let insuff := mkSliceWithBitsRefs (stripeBits available (bits % 2))
          expectSameOutcome s!"alias/cellund/bits-{bits}/avail-{available}"
            (runHandlerDirect execInstrCellLoadInt decodedShort #[.slice insuff])
            (runHandlerDirect execInstrCellLoadInt decodedAlt #[.slice insuff]) }
    ,
    { name := "unit/proxy/ldix-aligns-with-direct-ldi-alt-on-shared-domain"
      run := do
        let okChecks : Array (Nat × Slice) :=
          #[
            (1, mkLdiAltWordInput 1 1 tailBits3),
            (8, mkLdiAltWordInput 8 0x80 tailBits5),
            (32, mkLdiAltInput 32 tailBits7 0),
            (256, mkLdiAltInput 256 tailBits3 1)
          ]
        for (bits, input) in okChecks do
          expectSameOutcome s!"align/ok/bits-{bits}"
            (runLdiAltDirect bits #[.slice input])
            (runLdixDirect #[.slice input, intV bits])

        let insuff : Array (Nat × Nat) := #[(1, 0), (8, 7), (256, 255)]
        for (bits, available) in insuff do
          let slice := mkSliceWithBitsRefs (stripeBits available 0)
          expectSameOutcome s!"align/cellund/bits-{bits}/avail-{available}"
            (runLdiAltDirect bits #[.slice slice])
            (runLdixDirect #[.slice slice, intV bits])

        expectSameOutcome "align/underflow-empty"
          (runLdiAltDirect 8 #[])
          (runLdixDirect #[])
        expectSameOutcome "align/type-top-null"
          (runLdiAltDirect 8 #[.null])
          (runLdixDirect #[.null, intV 8])
        expectSameOutcome "align/type-deep-top-not-slice"
          (runLdiAltDirect 8 #[.slice (mkLdiAltInput 8 tailBits3 0), .null])
          (runLdixDirect #[.slice (mkLdiAltInput 8 tailBits3 0), .null, intV 8]) }
    ,
    { name := "unit/dispatch/non-loadint-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runLdiAltDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/loadint-var-neighbor"
          (runLdiAltDispatchFallback ldixInstr #[intV 11])
          #[intV 11, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-cell-op"
          (runLdiAltDispatchFallback .ldref #[.cell Cell.empty])
          #[.cell Cell.empty, intV dispatchSentinel] }
  ]
  oracle := #[
    mkLdiAltCase "ok/bits-1/zero" 1 #[.slice (mkLdiAltWordInput 1 0)],
    mkLdiAltCase "ok/bits-1/neg1" 1 #[.slice (mkLdiAltWordInput 1 1 tailBits7)],
    mkLdiAltCase "ok/bits-2/pos1-tail3" 2 #[.slice (mkLdiAltWordInput 2 1 tailBits3)],
    mkLdiAltCase "ok/bits-2/neg1" 2 #[.slice (mkLdiAltWordInput 2 3)],
    mkLdiAltCase "ok/bits-3/neg2-tail5" 3 #[.slice (mkLdiAltWordInput 3 6 tailBits5)],
    mkLdiAltCase "ok/bits-7/tail13-neg" 7 #[.slice (mkLdiAltInput 7 tailBits13 1)],
    mkLdiAltCase "ok/bits-8/zero" 8 #[.slice (mkLdiAltWordInput 8 0)],
    mkLdiAltCase "ok/bits-8/max-pos" 8 #[.slice (mkLdiAltWordInput 8 0x7f tailBits5)],
    mkLdiAltCase "ok/bits-8/min-neg" 8 #[.slice (mkLdiAltWordInput 8 0x80)],
    mkLdiAltCase "ok/bits-8/neg1-tail11" 8 #[.slice (mkLdiAltWordInput 8 0xff tailBits11)],
    mkLdiAltCase "ok/bits-15/exact-neg" 15 #[.slice (mkLdiAltInput 15 #[] 1)],
    mkLdiAltCase "ok/bits-16/max-pos" 16 #[.slice (mkLdiAltWordInput 16 0x7fff tailBits3)],
    mkLdiAltCase "ok/bits-16/min-neg" 16 #[.slice (mkLdiAltWordInput 16 0x8000)],
    mkLdiAltCase "ok/bits-31/exact-pos" 31 #[.slice (mkLdiAltInput 31 #[] 0)],
    mkLdiAltCase "ok/bits-63/tail5-neg" 63 #[.slice (mkLdiAltInput 63 tailBits5 1)],
    mkLdiAltCase "ok/bits-127/exact-neg" 127 #[.slice (mkLdiAltInput 127 #[] 1)],
    mkLdiAltCase "ok/bits-255/exact-pos" 255 #[.slice (mkLdiAltInput 255 #[] 0)],
    mkLdiAltCase "ok/bits-255/tail1-neg" 255 #[.slice (mkLdiAltInput 255 #[true] 1)],
    mkLdiAltCase "ok/bits-256/exact-neg" 256 #[.slice (mkLdiAltInput 256 #[] 1)],
    mkLdiAltCase "ok/bits-256/tail3-pos" 256 #[.slice (mkLdiAltInput 256 tailBits3 0)],
    mkLdiAltCase "ok/bits-8/refs2-neg" 8 #[.slice (mkLdiAltWordInput 8 0x80 tailBits5 #[refLeafA, refLeafB])],
    mkLdiAltCase "ok/bits-32/refs3-tail7-neg" 32
      #[.slice (mkLdiAltInput 32 tailBits7 1 #[refLeafA, refLeafB, refLeafC])],
    mkLdiAltCase "ok/deep-stack-preserve-neg1" 8
      #[.null, intV 42, .slice (mkLdiAltWordInput 8 0xff tailBits7)],
    mkLdiAltCase "ok/deep-stack-with-refs-pos" 32
      #[.cell Cell.empty, .slice (mkLdiAltInput 32 tailBits5 0 #[refLeafA])],

    mkLdiAltCase "cellund/bits-1/avail0" 1 #[.slice (mkSliceWithBitsRefs #[])],
    mkLdiAltCase "cellund/bits-8/avail7" 8 #[.slice (mkSliceWithBitsRefs (stripeBits 7 0))],
    mkLdiAltCase "cellund/bits-64/avail63" 64 #[.slice (mkSliceWithBitsRefs (stripeBits 63 1))],
    mkLdiAltCase "cellund/bits-255/avail254" 255 #[.slice (mkSliceWithBitsRefs (stripeBits 254 0))],
    mkLdiAltCase "cellund/bits-256/avail255" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))],
    mkLdiAltCase "cellund/bits-32/avail0-refs2" 32
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkLdiAltCase "cellund/refs-only-no-bits" 8
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA])],

    mkLdiAltRawCase "underflow/empty" #[],
    mkLdiAltCase "type/top-null" 8 #[.null],
    mkLdiAltCase "type/top-int" 8 #[intV 0],
    mkLdiAltCase "type/top-cell" 8 #[.cell Cell.empty],
    mkLdiAltCase "type/top-builder" 8 #[.builder Builder.empty],
    mkLdiAltCase "type/deep-top-not-slice" 8 #[.slice (mkLdiAltInput 8 tailBits3 0), .null],
    mkLdiAltCase "type/order-top-not-slice-over-short-slice" 8 #[.slice (mkSliceWithBitsRefs #[]), .null],

    mkLdiAltRawCase "gas/exact-cost-succeeds"
      #[.slice (mkLdiAltWordInput ldiAltGasProbeBits 0x80 tailBits11), intV ldiAltGasProbeBits]
      #[.pushInt (.num ldiAltProxySetGasExact), .tonEnvOp .setGasLimit, ldixInstr],
    mkLdiAltRawCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkLdiAltWordInput ldiAltGasProbeBits 0x80 tailBits11), intV ldiAltGasProbeBits]
      #[.pushInt (.num ldiAltProxySetGasExactMinusOne), .tonEnvOp .setGasLimit, ldixInstr]
  ]
  fuzz := #[
    { seed := 2026021083
      count := 320
      gen := genLdiAltFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDI_ALT
