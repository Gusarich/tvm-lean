import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDIQ

/-
LDIQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadInt.lean`
    (`.loadInt false false true bits`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.loadInt _ _ _ _ => .invOpcode`, var-form `.loadIntVar` encodable)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xd708>>3` fixed-width decode family for `{P}LD{I,U}{Q} <bits>`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_int_fixed2` → `exec_load_int_common`, mode args `4` for `LDIQ`).

Quiet fixed-width contract (non-prefetch + signed + quiet `LDIQ`) aligned to C++:
- success (`have(bits)`): push loaded signed int, then remainder slice, then `-1`;
- failure (`!have(bits)`): no exception, push original slice, then `0`;
- underflow/type failures happen when popping the source slice (after `bits==0` check);
- `bits==0` raises `rangeChk` before stack access.

Current Lean opcode-assembly mismatch:
- `decodeCp0` recognizes fixed-width `LDIQ` opcodes via `0xd708>>3`;
- `assembleCp0` currently rejects `.loadInt ...` with `.invOpcode`.
To keep oracle/fuzz coverage executable, this suite uses an oracle proxy program
(`LDIXQ` with explicit `bits` on stack), which executes the same C++ common load path.

Oracle harness constraint:
- oracle/fuzz inputs here use only full-cell slices (`bitPos=0`, `refPos=0`);
  partial-cursor slice coverage is included in direct unit tests only.
-/

private def ldiqId : InstrId := { name := "LDIQ" }

private def dispatchSentinel : Int := 929

private def ldiqInstr (bits : Nat) : Instr :=
  .loadInt false false true bits

private def ldixqInstr : Instr :=
  .loadIntVar false false true

private def ldiqProxyGasInstr : Instr :=
  ldixqInstr

private def mkLdiqProxyCase
    (name : String)
    (bits : Nat)
    (stackNoBits : Array Value)
    (program : Array Instr := #[ldixqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldiqId
    program := program
    initStack := stackNoBits.push (intV bits)
    gasLimits := gasLimits
    fuel := fuel }

private def mkLdiqProxyRawCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldixqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldiqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdiqDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt (ldiqInstr bits) stack

private def runLdiqDirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt instr stack

private def runLdixqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadIntVar ldixqInstr stack

private def runLdiqDispatchFallback (instr : Instr) (stack : Array Value) :
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

private def ldiqProxySetGasExact : Int :=
  computeExactGasBudget ldiqProxyGasInstr

private def ldiqProxySetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldiqProxyGasInstr

private def alternatingBits (n : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := n) fun i => (i.1 + phase) % 2 = 0

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3)

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 13 4)

private def mkSliceWithRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkPatternSlice (n : Nat) (phase : Nat := 0) : Slice :=
  mkSliceWithRefs (alternatingBits n phase)

private def mkPatternSliceWithRefs
    (n : Nat)
    (phase : Nat := 0)
    (refs : Array Cell := #[refLeafA]) : Slice :=
  mkSliceWithRefs (alternatingBits n phase) refs

private def sampleWidePos201 : Int := intPow2 199 + 654321
private def sampleWideNeg201 : Int := -(intPow2 200) + 123456

private def minSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else -(intPow2 (bits - 1))

private def maxSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 (bits - 1) - 1

private def signedBitsUnsafe (bits : Nat) (n : Int) : BitString :=
  match intToBitsTwos n bits with
  | .ok out => out
  | .error _ => panic! s!"signedBitsUnsafe: invalid n={n} for bits={bits}"

private def mkSignedSlice
    (bits : Nat)
    (n : Int)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithRefs (signedBitsUnsafe bits n ++ tail) refs

private def expectedSignedFromSlice (s : Slice) (bits : Nat) : Int :=
  bitsToIntSignedTwos (s.readBits bits)

private def loadIntWord24 (unsigned prefetch quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat := (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := 0xd708 >>> 3
  (prefix13 <<< 11) + args11

private def loadIntVarWord (unsigned prefetch quiet : Bool) : Nat :=
  let args3 : Nat := (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  0xd700 + args3

private def ldiqWidthBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickLdiqWidthBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (ldiqWidthBoundaryPool.size - 1)
  (ldiqWidthBoundaryPool[idx]!, rng')

private def pickLdiqWidthMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickLdiqWidthBoundary rng1
  else
    randNat rng1 1 256

private def pickLdiqAvailAtLeast (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let maxExtra : Nat := Nat.min 64 (1023 - bits)
  let (extra, rng1) := randNat rng0 0 maxExtra
  (bits + extra, rng1)

private def pickLdiqAvailBelow (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    randNat rng0 0 (bits - 1)

private def pickLdiqRefPackNonEmpty (rng0 : StdGen) : Array Cell × StdGen :=
  let (pick, rng1) := randNat rng0 0 1
  if pick = 0 then
    (#[refLeafA], rng1)
  else
    (#[refLeafA, refLeafB], rng1)

private def pickLdiqNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 19
    else .cell Cell.empty
  (v, rng1)

private def randBitString (bitCount : Nat) (rng0 : StdGen) : BitString × StdGen := Id.run do
  let mut bits : BitString := #[]
  let mut rng := rng0
  for _ in [0:bitCount] do
    let (bit, rng') := randBool rng
    bits := bits.push bit
    rng := rng'
  return (bits, rng)

private def pickSignedForWidth (bits : Nat) (rng0 : StdGen) : Int × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    let lo := minSignedBits bits
    let hi := maxSignedBits bits
    let (mode, rng1) := randNat rng0 0 8
    if mode = 0 then
      (0, rng1)
    else if mode = 1 then
      (-1, rng1)
    else if mode = 2 then
      (if hi ≥ 1 then 1 else hi, rng1)
    else if mode = 3 then
      (lo, rng1)
    else if mode = 4 then
      (hi, rng1)
    else if mode = 5 then
      (if lo < hi then lo + 1 else lo, rng1)
    else if mode = 6 then
      (if hi > lo then hi - 1 else hi, rng1)
    else
      let (raw, rng2) := randBitString bits rng1
      (bitsToIntSignedTwos raw, rng2)

private def pickTailBits (rng0 : StdGen) : BitString × StdGen :=
  let (tailLen, rng1) := randNat rng0 0 16
  randBitString tailLen rng1

private def genLdiqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (bits, rng2) := pickLdiqWidthMixed rng1
  if shape = 0 then
    let (x, rng3) := pickSignedForWidth bits rng2
    (mkLdiqProxyCase s!"fuzz/ok/exact/w-{bits}/x-{x}" bits #[.slice (mkSignedSlice bits x)], rng3)
  else if shape = 1 then
    let (x, rng3) := pickSignedForWidth bits rng2
    let (tail, rng4) := pickTailBits rng3
    (mkLdiqProxyCase s!"fuzz/ok/tail/w-{bits}/tail-{tail.size}" bits
      #[.slice (mkSignedSlice bits x tail)], rng4)
  else if shape = 2 then
    let (x, rng3) := pickSignedForWidth bits rng2
    let (tail, rng4) := pickTailBits rng3
    let (refs, rng5) := pickLdiqRefPackNonEmpty rng4
    (mkLdiqProxyCase s!"fuzz/ok/refs/w-{bits}/r-{refs.size}" bits
      #[.slice (mkSignedSlice bits x tail refs)], rng5)
  else if shape = 3 then
    let (x, rng3) := pickSignedForWidth bits rng2
    let (tail, rng4) := pickTailBits rng3
    let (noise, rng5) := pickLdiqNoiseValue rng4
    (mkLdiqProxyCase s!"fuzz/ok/deep-stack/w-{bits}" bits
      #[noise, .slice (mkSignedSlice bits x tail)], rng5)
  else if shape = 4 then
    let avail := bits - 1
    (mkLdiqProxyCase s!"fuzz/fail/by1/w-{bits}/a-{avail}" bits #[.slice (mkPatternSlice avail 0)], rng2)
  else if shape = 5 then
    let (avail, rng3) := pickLdiqAvailBelow bits rng2
    (mkLdiqProxyCase s!"fuzz/fail/short/w-{bits}/a-{avail}" bits #[.slice (mkPatternSlice avail 1)], rng3)
  else if shape = 6 then
    let (avail, rng3) := pickLdiqAvailBelow bits rng2
    let (refs, rng4) := pickLdiqRefPackNonEmpty rng3
    (mkLdiqProxyCase s!"fuzz/fail/short-refs/w-{bits}/a-{avail}/r-{refs.size}" bits
      #[.slice (mkPatternSliceWithRefs avail 0 refs)], rng4)
  else if shape = 7 then
    let (avail, rng3) := pickLdiqAvailBelow bits rng2
    let (noise, rng4) := pickLdiqNoiseValue rng3
    (mkLdiqProxyCase s!"fuzz/fail/deep-stack/w-{bits}/a-{avail}" bits
      #[noise, .slice (mkPatternSlice avail 1)], rng4)
  else if shape = 8 then
    (mkLdiqProxyRawCase "fuzz/underflow/empty" #[], rng2)
  else if shape = 9 then
    (mkLdiqProxyRawCase s!"fuzz/underflow/one-item/bits-{bits}" #[intV bits], rng2)
  else if shape = 10 then
    (mkLdiqProxyRawCase s!"fuzz/type/top-bits-not-int/bits-{bits}" #[.slice (mkPatternSlice bits), .null], rng2)
  else if shape = 11 then
    (mkLdiqProxyRawCase s!"fuzz/type/top-slice-not-slice/bits-{bits}" #[.null, intV bits], rng2)
  else if shape = 12 then
    (mkLdiqProxyRawCase "fuzz/range/bits-too-large" #[.slice (mkPatternSlice 16 1), intV 258], rng2)
  else if shape = 13 then
    (mkLdiqProxyRawCase "fuzz/range/bits-negative" #[.slice (mkPatternSlice 16 0), intV (-1)], rng2)
  else if shape = 14 then
    let (x, rng3) := pickSignedForWidth 8 rng2
    (mkLdiqProxyRawCase "fuzz/gas/exact"
      #[.slice (mkSignedSlice 8 x tailBits11), intV 8]
      #[.pushInt (.num ldiqProxySetGasExact), .tonEnvOp .setGasLimit, ldixqInstr], rng3)
  else if shape = 15 then
    let (x, rng3) := pickSignedForWidth 8 rng2
    (mkLdiqProxyRawCase "fuzz/gas/exact-minus-one"
      #[.slice (mkSignedSlice 8 x tailBits7), intV 8]
      #[.pushInt (.num ldiqProxySetGasExactMinusOne), .tonEnvOp .setGasLimit, ldixqInstr], rng3)
  else if shape = 16 then
    let bits' := if bits = 256 then 255 else bits
    let (x, rng3) := pickSignedForWidth bits' rng2
    let tail : BitString := #[true]
    (mkLdiqProxyCase s!"fuzz/ok/near-boundary/w-{bits'}-a-{bits' + 1}" bits'
      #[.slice (mkSignedSlice bits' x tail)], rng3)
  else if shape = 17 then
    let bits' := if bits = 1 then 2 else bits
    let avail := bits' - 1
    (mkLdiqProxyCase s!"fuzz/fail/near-boundary/w-{bits'}-a-{avail}" bits'
      #[.slice (mkPatternSlice avail 0)], rng2)
  else if shape = 18 then
    (mkLdiqProxyRawCase "fuzz/error-order/range-before-slice-pop" #[.null, intV 300], rng2)
  else if shape = 19 then
    (mkLdiqProxyRawCase "fuzz/error-order/bits-type-before-slice-pop" #[.null, .null], rng2)
  else if shape = 20 then
    let (avail, rng3) := pickLdiqAvailAtLeast 8 rng2
    (mkLdiqProxyRawCase "fuzz/range/bits-nan"
      #[.slice (mkPatternSlice avail 1)]
      #[.pushInt .nan, ldixqInstr], rng3)
  else
    let (avail, rng3) := pickLdiqAvailAtLeast bits rng2
    let (x, rng4) := pickSignedForWidth bits rng3
    let tail := alternatingBits (avail - bits) 1
    (mkLdiqProxyRawCase s!"fuzz/ok/raw-proxy/w-{bits}-a-{avail}"
      #[.slice (mkSignedSlice bits x tail), intV bits] #[ldixqInstr], rng4)

def suite : InstrSuite where
  id := ldiqId
  unit := #[
    { name := "unit/direct/quiet-success-pushes-signed-int-remainder-and-minus1"
      run := do
        let checks : Array (Nat × Int × BitString) :=
          #[
            (1, 0, #[]),
            (1, -1, tailBits7),
            (2, -2, #[]),
            (8, -128, tailBits5),
            (8, 127, #[]),
            (16, -32768, tailBits3),
            (16, 32767, tailBits7),
            (64, -(intPow2 63), tailBits11),
            (64, intPow2 63 - 1, #[]),
            (127, -(intPow2 126), #[]),
            (201, sampleWidePos201, #[]),
            (201, sampleWideNeg201, tailBits5),
            (255, intPow2 254 - 7, #[]),
            (255, -(intPow2 254), tailBits13),
            (256, -(intPow2 255), #[]),
            (256, intPow2 255 - 1, tailBits3)
          ]
        for (bits, n, tail) in checks do
          let input := mkSignedSlice bits n tail
          expectOkStack s!"ok/w-{bits}/n-{n}/tail-{tail.size}"
            (runLdiqDirect bits #[.slice input])
            #[intV n, .slice (input.advanceBits bits), intV (-1)]

        let refsInput := mkSignedSlice 8 (-42) tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs/w-8-n-neg42-r-2"
          (runLdiqDirect 8 #[.slice refsInput])
          #[intV (-42), .slice (refsInput.advanceBits 8), intV (-1)]

        let deep := mkSignedSlice 16 (-12345) tailBits11
        expectOkStack "ok/deep-stack-preserve-below"
          (runLdiqDirect 16 #[.null, intV 33, .slice deep])
          #[.null, intV 33, intV (-12345), .slice (deep.advanceBits 16), intV (-1)]

        let partialCell : Cell := Cell.mkOrdinary (alternatingBits 48 1) #[refLeafA, refLeafB]
        let partialSlice : Slice := { cell := partialCell, bitPos := 9, refPos := 1 }
        let expected := expectedSignedFromSlice partialSlice 12
        expectOkStack "ok/partial-slice-cursor"
          (runLdiqDirect 12 #[.slice partialSlice])
          #[intV expected, .slice (partialSlice.advanceBits 12), intV (-1)] }
    ,
    { name := "unit/direct/quiet-failure-preserves-original-slice-and-status0"
      run := do
        let checks : Array (Nat × Nat × Nat) :=
          #[
            (1, 0, 0),
            (2, 1, 1),
            (8, 7, 0),
            (16, 0, 1),
            (64, 63, 0),
            (128, 127, 1),
            (256, 255, 0)
          ]
        for (bits, avail, phase) in checks do
          let input := mkPatternSlice avail phase
          expectOkStack s!"fail/w-{bits}-a-{avail}"
            (runLdiqDirect bits #[.slice input])
            #[.slice input, intV 0]

        let refsInput := mkPatternSliceWithRefs 4 0 #[refLeafA, refLeafB]
        expectOkStack "fail/refs/w-5-a-4-r-2"
          (runLdiqDirect 5 #[.slice refsInput])
          #[.slice refsInput, intV 0]

        let deep := mkPatternSlice 10 1
        expectOkStack "fail/deep-stack-preserve-below"
          (runLdiqDirect 64 #[intV 77, .slice deep])
          #[intV 77, .slice deep, intV 0]

        let shortCursorCell : Cell := Cell.mkOrdinary (alternatingBits 24 0) #[refLeafA]
        let shortCursorSlice : Slice := { cell := shortCursorCell, bitPos := 20, refPos := 0 }
        expectOkStack "fail/partial-slice-short"
          (runLdiqDirect 5 #[.slice shortCursorSlice])
          #[.slice shortCursorSlice, intV 0]

        expectErr "nonquiet/short-throws-cellund"
          (runLdiqDirectInstr (.loadInt false false false 8) #[.slice (mkPatternSlice 7 0)]) .cellUnd }
    ,
    { name := "unit/direct/range-underflow-type-and-ordering"
      run := do
        expectErr "range/bits0-empty-stack"
          (runLdiqDirect 0 #[]) .rangeChk
        expectErr "range/bits0-top-not-slice"
          (runLdiqDirect 0 #[.null]) .rangeChk
        expectErr "range/bits0-valid-slice"
          (runLdiqDirect 0 #[.slice (mkPatternSlice 3 1)]) .rangeChk

        expectErr "underflow/empty"
          (runLdiqDirect 8 #[]) .stkUnd
        expectErr "type/top-null"
          (runLdiqDirect 8 #[.null]) .typeChk
        expectErr "type/top-int"
          (runLdiqDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell"
          (runLdiqDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder"
          (runLdiqDirect 8 #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdiqDirect 8 #[.slice (mkPatternSlice 8 0), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runLdiqDirect 8 #[.slice (mkPatternSlice 0 1), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-family-fixed-vs-short-and-asm-gap"
      run := do
        let rawFamily := mkSliceFromBits
          (natToBits (loadIntVarWord false false true) 16 ++
           natToBits (loadIntVarWord false true true) 16 ++
           natToBits (loadIntWord24 false false true 1) 24 ++
           natToBits (loadIntWord24 false false true 17) 24 ++
           natToBits (loadIntWord24 false false true 256) 24 ++
           natToBits (loadIntWord24 true false true 5) 24 ++
           natToBits (loadIntWord24 false true true 5) 24 ++
           natToBits (loadIntWord24 false false false 5) 24 ++
           natToBits 0xd204 16 ++
           natToBits 0xd710 16 ++
           natToBits 0xa0 8)
        let r1 ← expectDecodeStep "decode/raw-ldixq" rawFamily ldixqInstr 16
        let r2 ← expectDecodeStep "decode/raw-pldixq-neighbor" r1 (.loadIntVar false true true) 16
        let r3 ← expectDecodeStep "decode/raw-ldiq-1" r2 (ldiqInstr 1) 24
        let r4 ← expectDecodeStep "decode/raw-ldiq-17" r3 (ldiqInstr 17) 24
        let r5 ← expectDecodeStep "decode/raw-ldiq-256" r4 (ldiqInstr 256) 24
        let r6 ← expectDecodeStep "decode/raw-lduq-5" r5 (.loadInt true false true 5) 24
        let r7 ← expectDecodeStep "decode/raw-pldiq-5" r6 (.loadInt false true true 5) 24
        let r8 ← expectDecodeStep "decode/raw-ldi-5" r7 (.loadInt false false false 5) 24
        let r9 ← expectDecodeStep "decode/raw-short-ldi-5" r8 (.loadInt false false false 5) 16
        let r10 ← expectDecodeStep "decode/raw-boundary-plduz-0" r9 (.cellExt (.plduz 0)) 16
        let r11 ← expectDecodeStep "decode/raw-tail-add" r10 .add 8
        if r11.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r11.bitsRemaining} bits remaining")

        match assembleCp0 [ldiqInstr 8] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"asm/ldiq-fixed: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "asm/ldiq-fixed: expected invOpcode, got success")

        match assembleCp0 [ldiqInstr 256] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"asm/ldiq-fixed-256: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "asm/ldiq-fixed-256: expected invOpcode, got success")

        match assembleCp0 [ldiqInstr 0] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"asm/ldiq-fixed-0: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "asm/ldiq-fixed-0: expected invOpcode, got success")

        let proxySingle ←
          match assembleCp0 [ldixqInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/proxy-single failed: {e}")
        if proxySingle.bits = natToBits (loadIntVarWord false false true) 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/ldixq: expected 0xd704 encoding, got bits {proxySingle.bits}")

        let proxyCode ←
          match assembleCp0 [ldixqInstr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/proxy failed: {e}")
        let s0 := Slice.ofCell proxyCode
        let s1 ← expectDecodeStep "decode/proxy-ldixq" s0 ldixqInstr 16
        let s2 ← expectDecodeStep "decode/proxy-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/proxy-end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/proxy/ldixq-aligns-with-direct-ldiq-on-shared-domain"
      run := do
        let okChecks : Array (Nat × Int × BitString) :=
          #[
            (1, -1, tailBits3),
            (8, -42, tailBits5),
            (32, 123456, tailBits7),
            (256, -(intPow2 255) + 9, tailBits3)
          ]
        for (bits, n, tail) in okChecks do
          let input := mkSignedSlice bits n tail
          expectSameOutcome s!"align/ok/w-{bits}/n-{n}"
            (runLdiqDirect bits #[.slice input])
            (runLdixqDirect #[.slice input, intV bits])

        let failChecks : Array (Nat × Nat × Nat) :=
          #[(1, 0, 0), (8, 7, 1), (256, 255, 0)]
        for (bits, avail, phase) in failChecks do
          let input := mkPatternSlice avail phase
          expectSameOutcome s!"align/fail/w-{bits}/a-{avail}"
            (runLdiqDirect bits #[.slice input])
            (runLdixqDirect #[.slice input, intV bits])

        expectSameOutcome "align/underflow-empty"
          (runLdiqDirect 8 #[])
          (runLdixqDirect #[])
        expectSameOutcome "align/type-top-null"
          (runLdiqDirect 8 #[.null])
          (runLdixqDirect #[.null, intV 8])
        expectSameOutcome "align/type-deep-top-not-slice"
          (runLdiqDirect 8 #[.slice (mkPatternSlice 8 0), .null])
          (runLdixqDirect #[.slice (mkPatternSlice 8 0), .null, intV 8]) }
    ,
    { name := "unit/dispatch/non-loadint-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runLdiqDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/ldu-short-not-handled-here"
          (runLdiqDispatchFallback (.ldu 8) #[intV (-3)])
          #[intV (-3), intV dispatchSentinel]
        expectOkStack "dispatch/loadintvar-not-handled-here"
          (runLdiqDispatchFallback ldixqInstr #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/loadslice-neighbor-not-handled-here"
          (runLdiqDispatchFallback (.loadSliceFixed false true 8) #[.cell Cell.empty])
          #[.cell Cell.empty, intV dispatchSentinel] }
  ]
  oracle := #[
    mkLdiqProxyCase "ok/w-1-n-0-a-1" 1 #[.slice (mkSignedSlice 1 0)],
    mkLdiqProxyCase "ok/w-1-n-neg1-a-8" 1 #[.slice (mkSignedSlice 1 (-1) tailBits7)],
    mkLdiqProxyCase "ok/w-2-n-neg2-a-2" 2 #[.slice (mkSignedSlice 2 (-2))],
    mkLdiqProxyCase "ok/w-8-n-neg128-a-8" 8 #[.slice (mkSignedSlice 8 (-128))],
    mkLdiqProxyCase "ok/w-8-n-pos127-a-13" 8 #[.slice (mkSignedSlice 8 127 tailBits5)],
    mkLdiqProxyCase "ok/w-16-n-neg32768-a-16" 16 #[.slice (mkSignedSlice 16 (-32768))],
    mkLdiqProxyCase "ok/w-16-n-pos32767-a-23" 16 #[.slice (mkSignedSlice 16 32767 tailBits7)],
    mkLdiqProxyCase "ok/w-32-n-neg123456-a-35" 32 #[.slice (mkSignedSlice 32 (-123456) tailBits3)],
    mkLdiqProxyCase "ok/w-64-n-posmax-a-64" 64 #[.slice (mkSignedSlice 64 (intPow2 63 - 1))],
    mkLdiqProxyCase "ok/w-64-n-min-a-71" 64 #[.slice (mkSignedSlice 64 (-(intPow2 63)) tailBits7)],
    mkLdiqProxyCase "ok/w-127-n-negmin-a-127" 127 #[.slice (mkSignedSlice 127 (-(intPow2 126)))],
    mkLdiqProxyCase "ok/w-128-n-posmax-a-133" 128 #[.slice (mkSignedSlice 128 (intPow2 127 - 1) tailBits5)],
    mkLdiqProxyCase "ok/w-201-sample-pos-a-201" 201 #[.slice (mkSignedSlice 201 sampleWidePos201)],
    mkLdiqProxyCase "ok/w-201-sample-neg-a-208" 201 #[.slice (mkSignedSlice 201 sampleWideNeg201 tailBits7)],
    mkLdiqProxyCase "ok/w-255-near-max-a-255" 255 #[.slice (mkSignedSlice 255 (intPow2 254 - 7))],
    mkLdiqProxyCase "ok/w-256-min-a-256" 256 #[.slice (mkSignedSlice 256 (-(intPow2 255)))],
    mkLdiqProxyCase "ok/w-256-max-a-259" 256 #[.slice (mkSignedSlice 256 (intPow2 255 - 1) tailBits3)],
    mkLdiqProxyCase "ok/deep-stack/w-16-n-neg5-a-23" 16 #[.null, intV 42, .slice (mkSignedSlice 16 (-5) tailBits7)],
    mkLdiqProxyCase "ok/refs/w-8-n-neg42-a-13-r-2" 8
      #[.slice (mkSignedSlice 8 (-42) tailBits5 #[refLeafA, refLeafB])],
    mkLdiqProxyCase "ok/refs/w-256-min-a-259-r-1" 256
      #[.slice (mkSignedSlice 256 (-(intPow2 255)) tailBits3 #[refLeafA])],

    mkLdiqProxyCase "fail/w-1-a-0" 1 #[.slice (mkPatternSlice 0 0)],
    mkLdiqProxyCase "fail/w-2-a-1" 2 #[.slice (mkPatternSlice 1 1)],
    mkLdiqProxyCase "fail/w-8-a-7" 8 #[.slice (mkPatternSlice 7 0)],
    mkLdiqProxyCase "fail/w-16-a-0" 16 #[.slice (mkPatternSlice 0 1)],
    mkLdiqProxyCase "fail/w-64-a-63" 64 #[.slice (mkPatternSlice 63 0)],
    mkLdiqProxyCase "fail/w-128-a-127" 128 #[.slice (mkPatternSlice 127 1)],
    mkLdiqProxyCase "fail/w-256-a-255" 256 #[.slice (mkPatternSlice 255 0)],
    mkLdiqProxyCase "fail/deep-stack/w-64-a-10" 64 #[intV 33, .slice (mkPatternSlice 10 1)],
    mkLdiqProxyCase "fail/refs/w-5-a-4-r-1" 5 #[.slice (mkPatternSliceWithRefs 4 0 #[refLeafA])],
    mkLdiqProxyCase "fail/refs/w-256-a-128-r-2" 256
      #[.slice (mkPatternSliceWithRefs 128 1 #[refLeafA, refLeafB])],

    mkLdiqProxyRawCase "underflow/empty" #[],
    mkLdiqProxyRawCase "underflow/one-item" #[intV 8],
    mkLdiqProxyRawCase "type/top-bits-not-int" #[.slice (mkPatternSlice 8 0), .null],
    mkLdiqProxyRawCase "type/top-slice-not-slice" #[.null, intV 8],
    mkLdiqProxyRawCase "range/bits-too-large" #[.slice (mkPatternSlice 16 1), intV 258],
    mkLdiqProxyRawCase "range/bits-negative" #[.slice (mkPatternSlice 16 0), intV (-1)],
    mkLdiqProxyRawCase "error-order/range-before-slice-pop" #[.null, intV 300],
    mkLdiqProxyRawCase "error-order/bits-type-before-slice-pop" #[.null, .null],

    mkLdiqProxyRawCase "gas/exact-cost-succeeds"
      #[.slice (mkSignedSlice 8 (-5) tailBits11), intV 8]
      #[.pushInt (.num ldiqProxySetGasExact), .tonEnvOp .setGasLimit, ldixqInstr],
    mkLdiqProxyRawCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkSignedSlice 8 7 tailBits11), intV 8]
      #[.pushInt (.num ldiqProxySetGasExactMinusOne), .tonEnvOp .setGasLimit, ldixqInstr]
  ]
  fuzz := #[
    { seed := 2026021116
      count := 500
      gen := genLdiqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDIQ
