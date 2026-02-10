import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDI

/-
LDI branch-mapping notes (fixed-width, non-prefetch, signed, non-quiet):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadInt.lean`
    (`.loadInt false false false bits`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (short `0xd2xx` decode + fixed2 `0xd708>>3` decode family)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.loadInt _ _ _ _` currently rejects assembly with `.invOpcode`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_int_fixed`, `exec_load_int_fixed2`, `exec_load_int_common`, mode=`0`).

Branch map used for this suite (`LDI` = signed, non-prefetch, non-quiet):
- bits==0 guard: immediate `rangeChk` before any stack read;
- stack underflow/type from `popSlice` when bits>0;
- success (`have(bits)`): push signed integer then remainder slice;
- failure (`!have(bits)`): throw `cellUnd` (non-quiet);
- handler dispatch fallthrough for non-`.loadInt` instructions;
- decode boundaries across short `0xd2xx` and fixed2 `0xd708>>3` families.

Assembler note:
- `decodeCp0` recognizes both short `LDI` (`0xd2xx`) and fixed2 load-int opcodes,
  but `assembleCp0` currently rejects `.loadInt _ _ _ _` with `.invOpcode`.
- Oracle/fuzz therefore use `LDIX` (`.loadIntVar false false false`) as the closest
  executable proxy (same C++ `exec_load_int_common` path on shared bits domain).
- Direct unit tests keep immediate-width LDI behavior and decode-family boundaries covered.
-/

private def ldiId : InstrId := { name := "LDI" }

private def dispatchSentinel : Int := 947

private def ldiInstr (bits : Nat) : Instr :=
  .loadInt false false false bits

private def ldixInstr : Instr :=
  .loadIntVar false false false

private def ldiProxyGasInstr : Instr :=
  ldixInstr

private def loadIntFixedWord (unsigned prefetch quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat :=
    (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := (0xd708 >>> 3)
  (prefix13 <<< 11) + args11

private def ldiFixed2Word (bits : Nat) : Nat :=
  loadIntFixedWord false false false bits

private def ldiShortWord (bits : Nat) : Nat :=
  0xd200 + (bits - 1)

private def lduShortWord (bits : Nat) : Nat :=
  0xd300 + (bits - 1)

private def mkLdiCase
    (name : String)
    (bits : Nat)
    (stackNoBits : Array Value)
    (program : Array Instr := #[ldixInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldiId
    program := program
    initStack := stackNoBits.push (intV bits)
    gasLimits := gasLimits
    fuel := fuel }

private def mkLdiRawCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldixInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldiId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdiDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt (ldiInstr bits) stack

private def runLdixDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadIntVar ldixInstr stack

private def runLdiDispatchFallback (instr : Instr) (stack : Array Value) :
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

private def mkLdiInput
    (bits : Nat)
    (tail : BitString := #[])
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase ++ tail) refs

private def mkLdiWordInput
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

private def ldiGasProbeBits : Nat := 8

private def ldiProxySetGasExact : Int :=
  computeExactGasBudget ldiProxyGasInstr

private def ldiProxySetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldiProxyGasInstr

private def ldiBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickLdiBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (ldiBitsBoundaryPool.size - 1)
  (ldiBitsBoundaryPool[idx]!, rng')

private def pickLdiBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickLdiBitsBoundary rng1
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

private def genLdiFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 25
  let (bits, rng2) := pickLdiBitsMixed rng1
  let (phase, rng3) := randNat rng2 0 1
  if shape = 0 then
    (mkLdiCase s!"fuzz/ok/exact/bits-{bits}" bits
      #[.slice (mkLdiInput bits #[] phase)], rng3)
  else if shape = 1 then
    let (tailLen, rng4) := randNat rng3 1 24
    let tail := stripeBits tailLen (phase + 1)
    (mkLdiCase s!"fuzz/ok/tail/bits-{bits}/tail-{tailLen}" bits
      #[.slice (mkLdiInput bits tail phase)], rng4)
  else if shape = 2 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (refs, rng5) := pickRefPack rng4
    (mkLdiCase s!"fuzz/ok/refs/bits-{bits}/tail-{tailLen}/refs-{refs.size}" bits
      #[.slice (mkLdiInput bits tail phase refs)], rng5)
  else if shape = 3 then
    let (tailLen, rng4) := randNat rng3 0 16
    let tail := stripeBits tailLen (phase + 1)
    let (noise, rng5) := pickNoise rng4
    (mkLdiCase s!"fuzz/ok/deep/bits-{bits}/tail-{tailLen}" bits
      #[noise, .slice (mkLdiInput bits tail phase)], rng5)
  else if shape = 4 then
    let available := bits - 1
    (mkLdiCase s!"fuzz/cellund/by1/bits-{bits}/avail-{available}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits available phase))], rng3)
  else if shape = 5 then
    let maxDelta := Nat.min bits 8
    let (delta, rng4) := randNat rng3 1 maxDelta
    let available := bits - delta
    let (refs, rng5) := pickRefPack rng4
    (mkLdiCase s!"fuzz/cellund/delta-{delta}/bits-{bits}/avail-{available}" bits
      #[.slice (mkSliceWithBitsRefs (stripeBits available phase) refs)], rng5)
  else if shape = 6 then
    (mkLdiCase s!"fuzz/cellund/empty-slice/bits-{bits}" bits #[.slice (mkSliceFromBits #[])], rng3)
  else if shape = 7 then
    let (refs, rng4) := pickRefPack rng3
    (mkLdiCase s!"fuzz/cellund/refs-only/bits-{bits}/refs-{refs.size}" bits
      #[.slice (mkSliceWithBitsRefs #[] refs)], rng4)
  else if shape = 8 then
    (mkLdiRawCase "fuzz/underflow/empty" #[], rng3)
  else if shape = 9 then
    (mkLdiRawCase s!"fuzz/underflow/one-item-width-{bits}" #[intV bits], rng3)
  else if shape = 10 then
    (mkLdiCase s!"fuzz/type/top-null/bits-{bits}" bits #[.null], rng3)
  else if shape = 11 then
    (mkLdiCase s!"fuzz/type/top-int/bits-{bits}" bits #[intV 0], rng3)
  else if shape = 12 then
    (mkLdiCase s!"fuzz/type/top-cell/bits-{bits}" bits #[.cell Cell.empty], rng3)
  else if shape = 13 then
    (mkLdiCase s!"fuzz/type/top-builder/bits-{bits}" bits #[.builder Builder.empty], rng3)
  else if shape = 14 then
    (mkLdiCase s!"fuzz/type/deep-top-not-slice/bits-{bits}" bits
      #[.slice (mkLdiInput bits tailBits3 phase), .null], rng3)
  else if shape = 15 then
    (mkLdiCase "fuzz/signed/bits1/neg1" 1 #[.slice (mkLdiWordInput 1 1 tailBits3)], rng3)
  else if shape = 16 then
    (mkLdiCase "fuzz/signed/bits8/max-pos" 8 #[.slice (mkLdiWordInput 8 0x7f tailBits5)], rng3)
  else if shape = 17 then
    (mkLdiCase "fuzz/signed/bits8/min-neg" 8 #[.slice (mkLdiWordInput 8 0x80 tailBits7)], rng3)
  else if shape = 18 then
    (mkLdiCase "fuzz/signed/bits16/min-neg" 16 #[.slice (mkLdiWordInput 16 0x8000 tailBits3)], rng3)
  else if shape = 19 then
    (mkLdiCase "fuzz/ok/max-boundary-neg" 256 #[.slice (mkLdiInput 256 tailBits5 1)], rng3)
  else if shape = 20 then
    (mkLdiCase "fuzz/cellund/max-by1" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))], rng3)
  else if shape = 21 then
    (mkLdiRawCase "fuzz/range/bits-too-large"
      #[.slice (mkLdiInput 8 tailBits3 0), intV 258], rng3)
  else if shape = 22 then
    (mkLdiRawCase "fuzz/range/bits-negative"
      #[.slice (mkLdiInput 8 tailBits5 1), intV (-1)], rng3)
  else if shape = 23 then
    (mkLdiRawCase "fuzz/range/bits-nan"
      #[.slice (mkLdiInput 8 tailBits7 0)]
      #[.pushInt .nan, ldixInstr], rng3)
  else if shape = 24 then
    (mkLdiRawCase "fuzz/gas/exact"
      #[.slice (mkLdiWordInput ldiGasProbeBits 0x80 tailBits11), intV ldiGasProbeBits]
      #[.pushInt (.num ldiProxySetGasExact), .tonEnvOp .setGasLimit, ldixInstr], rng3)
  else
    (mkLdiRawCase "fuzz/gas/exact-minus-one"
      #[.slice (mkLdiWordInput ldiGasProbeBits 0x80 tailBits11), intV ldiGasProbeBits]
      #[.pushInt (.num ldiProxySetGasExactMinusOne), .tonEnvOp .setGasLimit, ldixInstr], rng3)

def suite : InstrSuite where
  id := ldiId
  unit := #[
    { name := "unit/direct/success-pushes-signed-int-then-remainder"
      run := do
        let checks : Array (Nat × Slice) :=
          #[
            (1, mkLdiWordInput 1 0),
            (1, mkLdiWordInput 1 1 tailBits7),
            (2, mkLdiWordInput 2 1 tailBits3),
            (2, mkLdiWordInput 2 3),
            (8, mkLdiWordInput 8 0),
            (8, mkLdiWordInput 8 0x7f tailBits5),
            (8, mkLdiWordInput 8 0x80),
            (8, mkLdiWordInput 8 0xff tailBits11),
            (16, mkLdiWordInput 16 0x7fff tailBits3),
            (16, mkLdiWordInput 16 0x8000),
            (255, mkLdiInput 255 #[] 0),
            (255, mkLdiInput 255 #[true] 1),
            (256, mkLdiInput 256 #[] 1),
            (256, mkLdiInput 256 tailBits3 0)
          ]
        for (bits, input) in checks do
          expectOkStack s!"ok/bits-{bits}/len-{input.bitsRemaining}"
            (runLdiDirect bits #[.slice input])
            #[intV (expectedSigned input bits), .slice (input.advanceBits bits)]

        let refsInput := mkLdiWordInput 8 0x80 tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs-preserved-in-remainder"
          (runLdiDirect 8 #[.slice refsInput])
          #[intV (expectedSigned refsInput 8), .slice (refsInput.advanceBits 8)]

        let deepInput := mkLdiWordInput 16 0x8001 tailBits7
        expectOkStack "ok/deep-stack-preserved"
          (runLdiDirect 16 #[.null, intV 99, .slice deepInput])
          #[.null, intV 99, intV (expectedSigned deepInput 16), .slice (deepInput.advanceBits 16)]

        expectOkStack "ok/partial-slice-cursor"
          (runLdiDirect 12 #[.slice partialCursorSlice])
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
            (runLdiDirect bits #[.slice slice]) .cellUnd

        let refsOnly := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB]
        expectErr "cellund/refs-only-no-bits"
          (runLdiDirect 8 #[.slice refsOnly]) .cellUnd

        expectErr "cellund/partial-cursor-bits5-avail4"
          (runLdiDirect 5 #[.slice shortCursorSlice]) .cellUnd }
    ,
    { name := "unit/direct/range-underflow-type-and-ordering"
      run := do
        expectErr "range/bits0-empty-stack"
          (runLdiDirect 0 #[]) .rangeChk
        expectErr "range/bits0-top-not-slice"
          (runLdiDirect 0 #[.null]) .rangeChk
        expectErr "range/bits0-valid-slice"
          (runLdiDirect 0 #[.slice (mkLdiInput 1 #[] 0)]) .rangeChk

        expectErr "underflow/empty"
          (runLdiDirect 8 #[]) .stkUnd
        expectErr "type/top-null"
          (runLdiDirect 8 #[.null]) .typeChk
        expectErr "type/top-int"
          (runLdiDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell"
          (runLdiDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder"
          (runLdiDirect 8 #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdiDirect 8 #[.slice (mkLdiInput 8 tailBits3 0), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runLdiDirect 8 #[.slice (mkSliceWithBitsRefs #[]), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-boundaries-and-assembler-constraints"
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

        match assembleCp0 [ldiInstr 1] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/ldi-1: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/ldi-1: expected invOpcode, got success")

        match assembleCp0 [ldiInstr 256] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/ldi-256: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/ldi-256: expected invOpcode, got success")

        match assembleCp0 [ldiInstr 0] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/ldi-0: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/ldi-0: expected invOpcode, got success")

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
        let s2 ← expectDecodeStep "decode/raw-short-ldi-1" s1 (ldiInstr 1) 16
        let s3 ← expectDecodeStep "decode/raw-short-ldi-8" s2 (ldiInstr 8) 16
        let s4 ← expectDecodeStep "decode/raw-short-ldi-256" s3 (ldiInstr 256) 16
        let s5 ← expectDecodeStep "decode/raw-short-ldu-8-neighbor" s4 (.ldu 8) 16
        let s6 ← expectDecodeStep "decode/raw-short-tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-short-end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        let fixedRawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd707 16 ++
             natToBits (ldiFixed2Word 1) 24 ++
             natToBits (loadIntFixedWord true false false 8) 24 ++
             natToBits (loadIntFixedWord false true false 8) 24 ++
             natToBits (loadIntFixedWord false false true 8) 24 ++
             natToBits (ldiFixed2Word 256) 24 ++
             natToBits 0xd710 16 ++
             addCell.bits) #[]
        let f0 := Slice.ofCell fixedRawCode
        let f1 ← expectDecodeStep "decode/raw-fixed-boundary-plduxq" f0 (.loadIntVar true true true) 16
        let f2 ← expectDecodeStep "decode/raw-fixed-ldi-1" f1 (ldiInstr 1) 24
        let f3 ← expectDecodeStep "decode/raw-fixed-ldu-8-neighbor" f2 (.loadInt true false false 8) 24
        let f4 ← expectDecodeStep "decode/raw-fixed-pldi-8-neighbor" f3 (.loadInt false true false 8) 24
        let f5 ← expectDecodeStep "decode/raw-fixed-ldiq-8-neighbor" f4 (.loadInt false false true 8) 24
        let f6 ← expectDecodeStep "decode/raw-fixed-ldi-256" f5 (ldiInstr 256) 24
        let f7 ← expectDecodeStep "decode/raw-fixed-boundary-plduz-0" f6 (.cellExt (.plduz 0)) 16
        let f8 ← expectDecodeStep "decode/raw-fixed-tail-add" f7 .add 8
        if f8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-fixed-end: expected exhausted slice, got {f8.bitsRemaining} bits remaining") }
    ,
    { name := "unit/proxy/ldix-aligns-with-direct-ldi-on-shared-domain"
      run := do
        let okChecks : Array (Nat × Slice) :=
          #[
            (1, mkLdiWordInput 1 1 tailBits3),
            (8, mkLdiWordInput 8 0x80 tailBits5),
            (32, mkLdiInput 32 tailBits7 0),
            (256, mkLdiInput 256 tailBits3 1)
          ]
        for (bits, input) in okChecks do
          expectSameOutcome s!"align/ok/bits-{bits}"
            (runLdiDirect bits #[.slice input])
            (runLdixDirect #[.slice input, intV bits])

        let insuff : Array (Nat × Nat) := #[(1, 0), (8, 7), (256, 255)]
        for (bits, available) in insuff do
          let slice := mkSliceWithBitsRefs (stripeBits available 0)
          expectSameOutcome s!"align/cellund/bits-{bits}/avail-{available}"
            (runLdiDirect bits #[.slice slice])
            (runLdixDirect #[.slice slice, intV bits])

        expectSameOutcome "align/underflow-empty"
          (runLdiDirect 8 #[])
          (runLdixDirect #[])
        expectSameOutcome "align/type-top-null"
          (runLdiDirect 8 #[.null])
          (runLdixDirect #[.null, intV 8])
        expectSameOutcome "align/type-deep-top-not-slice"
          (runLdiDirect 8 #[.slice (mkLdiInput 8 tailBits3 0), .null])
          (runLdixDirect #[.slice (mkLdiInput 8 tailBits3 0), .null, intV 8]) }
    ,
    { name := "unit/dispatch/non-loadint-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runLdiDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/loadint-var-neighbor"
          (runLdiDispatchFallback ldixInstr #[intV 11])
          #[intV 11, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-cell-op"
          (runLdiDispatchFallback .ldref #[.cell Cell.empty])
          #[.cell Cell.empty, intV dispatchSentinel] }
  ]
  oracle := #[
    mkLdiCase "ok/bits-1/zero" 1 #[.slice (mkLdiWordInput 1 0)],
    mkLdiCase "ok/bits-1/neg1" 1 #[.slice (mkLdiWordInput 1 1 tailBits7)],
    mkLdiCase "ok/bits-2/pos1-tail3" 2 #[.slice (mkLdiWordInput 2 1 tailBits3)],
    mkLdiCase "ok/bits-2/neg1" 2 #[.slice (mkLdiWordInput 2 3)],
    mkLdiCase "ok/bits-3/neg2-tail5" 3 #[.slice (mkLdiWordInput 3 6 tailBits5)],
    mkLdiCase "ok/bits-7/tail13-neg" 7 #[.slice (mkLdiInput 7 tailBits13 1)],
    mkLdiCase "ok/bits-8/zero" 8 #[.slice (mkLdiWordInput 8 0)],
    mkLdiCase "ok/bits-8/max-pos" 8 #[.slice (mkLdiWordInput 8 0x7f tailBits5)],
    mkLdiCase "ok/bits-8/min-neg" 8 #[.slice (mkLdiWordInput 8 0x80)],
    mkLdiCase "ok/bits-8/neg1-tail11" 8 #[.slice (mkLdiWordInput 8 0xff tailBits11)],
    mkLdiCase "ok/bits-15/exact-neg" 15 #[.slice (mkLdiInput 15 #[] 1)],
    mkLdiCase "ok/bits-16/max-pos" 16 #[.slice (mkLdiWordInput 16 0x7fff tailBits3)],
    mkLdiCase "ok/bits-16/min-neg" 16 #[.slice (mkLdiWordInput 16 0x8000)],
    mkLdiCase "ok/bits-31/exact-pos" 31 #[.slice (mkLdiInput 31 #[] 0)],
    mkLdiCase "ok/bits-63/tail5-neg" 63 #[.slice (mkLdiInput 63 tailBits5 1)],
    mkLdiCase "ok/bits-127/exact-neg" 127 #[.slice (mkLdiInput 127 #[] 1)],
    mkLdiCase "ok/bits-255/exact-pos" 255 #[.slice (mkLdiInput 255 #[] 0)],
    mkLdiCase "ok/bits-255/tail1-neg" 255 #[.slice (mkLdiInput 255 #[true] 1)],
    mkLdiCase "ok/bits-256/exact-neg" 256 #[.slice (mkLdiInput 256 #[] 1)],
    mkLdiCase "ok/bits-256/tail3-pos" 256 #[.slice (mkLdiInput 256 tailBits3 0)],
    mkLdiCase "ok/bits-8/refs2-neg" 8 #[.slice (mkLdiWordInput 8 0x80 tailBits5 #[refLeafA, refLeafB])],
    mkLdiCase "ok/bits-32/refs3-tail7-neg" 32
      #[.slice (mkLdiInput 32 tailBits7 1 #[refLeafA, refLeafB, refLeafC])],
    mkLdiCase "ok/deep-stack-preserve-neg1" 8
      #[.null, intV 42, .slice (mkLdiWordInput 8 0xff tailBits7)],
    mkLdiCase "ok/deep-stack-with-refs-pos" 32
      #[.cell Cell.empty, .slice (mkLdiInput 32 tailBits5 0 #[refLeafA])],

    mkLdiCase "cellund/bits-1/avail0" 1 #[.slice (mkSliceWithBitsRefs #[])],
    mkLdiCase "cellund/bits-8/avail7" 8 #[.slice (mkSliceWithBitsRefs (stripeBits 7 0))],
    mkLdiCase "cellund/bits-64/avail63" 64 #[.slice (mkSliceWithBitsRefs (stripeBits 63 1))],
    mkLdiCase "cellund/bits-255/avail254" 255 #[.slice (mkSliceWithBitsRefs (stripeBits 254 0))],
    mkLdiCase "cellund/bits-256/avail255" 256 #[.slice (mkSliceWithBitsRefs (stripeBits 255 1))],
    mkLdiCase "cellund/bits-32/avail0-refs2" 32
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA, refLeafB])],
    mkLdiCase "cellund/refs-only-no-bits" 8
      #[.slice (mkSliceWithBitsRefs #[] #[refLeafA])],

    mkLdiRawCase "underflow/empty" #[],
    mkLdiCase "type/top-null" 8 #[.null],
    mkLdiCase "type/top-int" 8 #[intV 0],
    mkLdiCase "type/top-cell" 8 #[.cell Cell.empty],
    mkLdiCase "type/top-builder" 8 #[.builder Builder.empty],
    mkLdiCase "type/deep-top-not-slice" 8 #[.slice (mkLdiInput 8 tailBits3 0), .null],
    mkLdiCase "type/order-top-not-slice-over-short-slice" 8 #[.slice (mkSliceWithBitsRefs #[]), .null],

    mkLdiRawCase "gas/exact-cost-succeeds"
      #[.slice (mkLdiWordInput ldiGasProbeBits 0x80 tailBits11), intV ldiGasProbeBits]
      #[.pushInt (.num ldiProxySetGasExact), .tonEnvOp .setGasLimit, ldixInstr],
    mkLdiRawCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkLdiWordInput ldiGasProbeBits 0x80 tailBits11), intV ldiGasProbeBits]
      #[.pushInt (.num ldiProxySetGasExactMinusOne), .tonEnvOp .setGasLimit, ldixInstr]
  ]
  fuzz := #[
    { seed := 2026021074
      count := 320
      gen := genLdiFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDI
