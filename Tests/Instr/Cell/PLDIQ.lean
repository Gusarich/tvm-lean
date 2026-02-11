import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDIQ

/-
PLDIQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadInt.lean`
    (`.loadInt false true true bits`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.loadInt _ _ _ _ => .invOpcode`, var-form `.loadIntVar` encodable)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xd708>>3` decode family for fixed `{P}LD{I,U}{Q} <bits>`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_int_fixed2` → `exec_load_int_common`, mode args `6` for `PLDIQ`).

Quiet fixed-width contract (prefetch + signed + quiet `PLDIQ`) verified against C++:
- success (`have(bits)`): push loaded signed int, then `-1`; no remainder slice in prefetch mode;
- failure (`!have(bits)`): no exception, push only `0` (no slice re-push in prefetch mode);
- underflow/type failures happen at the initial slice pop, before quiet status behavior;
- `bits==0` raises `rangeChk` before any stack pop.

Current Lean opcode-assembly mismatch:
- `decodeCp0` recognizes fixed-width `PLDIQ` opcodes via `0xd708>>3`;
- `assembleCp0` currently rejects `.loadInt ...` with `.invOpcode`.
To keep oracle/fuzz coverage executable, this suite uses an oracle proxy program
(`PLDIXQ` with explicit `bits` on stack), which exercises the same C++ common load path.
-/

private def pldiqId : InstrId := { name := "PLDIQ" }

private def dispatchSentinel : Int := 923

private def pldiqInstr (bits : Nat) : Instr :=
  .loadInt false true true bits

private def pldixqInstr : Instr :=
  .loadIntVar false true true

private def pldiqProxyGasInstr : Instr :=
  pldixqInstr

private def mkPldiqProxyCase
    (name : String)
    (bits : Nat)
    (stackNoBits : Array Value)
    (program : Array Instr := #[pldixqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldiqId
    program := program
    initStack := stackNoBits.push (intV bits)
    gasLimits := gasLimits
    fuel := fuel }

private def mkPldiqProxyRawCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[pldixqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldiqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPldiqDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt (pldiqInstr bits) stack

private def runPldiqDirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt instr stack

private def runPldiqDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadInt instr (VM.push (intV dispatchSentinel)) stack

private def pldiqProxySetGasExact : Int :=
  computeExactGasBudget pldiqProxyGasInstr

private def pldiqProxySetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pldiqProxyGasInstr

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

private def pldiqWidthBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickPldiqWidthBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pldiqWidthBoundaryPool.size - 1)
  (pldiqWidthBoundaryPool[idx]!, rng')

private def pickPldiqWidthMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickPldiqWidthBoundary rng1
  else
    randNat rng1 1 256

private def pickPldiqAvailAtLeast (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let maxExtra : Nat := Nat.min 64 (1023 - bits)
  let (extra, rng1) := randNat rng0 0 maxExtra
  (bits + extra, rng1)

private def pickPldiqAvailBelow (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    randNat rng0 0 (bits - 1)

private def pickPldiqRefPackNonEmpty (rng0 : StdGen) : Array Cell × StdGen :=
  let (pick, rng1) := randNat rng0 0 1
  if pick = 0 then
    (#[refLeafA], rng1)
  else
    (#[refLeafA, refLeafB], rng1)

private def pickPldiqNoiseValue (rng0 : StdGen) : Value × StdGen :=
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
      (1, rng1)
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

private def genPldiqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (bits, rng2) := pickPldiqWidthMixed rng1
  if shape = 0 then
    let (x, rng3) := pickSignedForWidth bits rng2
    (mkPldiqProxyCase s!"fuzz/ok/exact/w-{bits}/x-{x}" bits #[.slice (mkSignedSlice bits x)], rng3)
  else if shape = 1 then
    let (x, rng3) := pickSignedForWidth bits rng2
    let (tail, rng4) := pickTailBits rng3
    (mkPldiqProxyCase s!"fuzz/ok/tail/w-{bits}/tail-{tail.size}" bits
      #[.slice (mkSignedSlice bits x tail)], rng4)
  else if shape = 2 then
    let (x, rng3) := pickSignedForWidth bits rng2
    let (tail, rng4) := pickTailBits rng3
    let (refs, rng5) := pickPldiqRefPackNonEmpty rng4
    (mkPldiqProxyCase s!"fuzz/ok/refs/w-{bits}/r-{refs.size}" bits
      #[.slice (mkSignedSlice bits x tail refs)], rng5)
  else if shape = 3 then
    let (x, rng3) := pickSignedForWidth bits rng2
    let (tail, rng4) := pickTailBits rng3
    let (noise, rng5) := pickPldiqNoiseValue rng4
    (mkPldiqProxyCase s!"fuzz/ok/deep-stack/w-{bits}" bits
      #[noise, .slice (mkSignedSlice bits x tail)], rng5)
  else if shape = 4 then
    let avail := bits - 1
    (mkPldiqProxyCase s!"fuzz/fail/by1/w-{bits}/a-{avail}" bits #[.slice (mkPatternSlice avail)], rng2)
  else if shape = 5 then
    let (avail, rng3) := pickPldiqAvailBelow bits rng2
    (mkPldiqProxyCase s!"fuzz/fail/short/w-{bits}/a-{avail}" bits #[.slice (mkPatternSlice avail 1)], rng3)
  else if shape = 6 then
    let (avail, rng3) := pickPldiqAvailBelow bits rng2
    let (refs, rng4) := pickPldiqRefPackNonEmpty rng3
    (mkPldiqProxyCase s!"fuzz/fail/short-refs/w-{bits}/a-{avail}/r-{refs.size}" bits
      #[.slice (mkPatternSliceWithRefs avail 0 refs)], rng4)
  else if shape = 7 then
    let (avail, rng3) := pickPldiqAvailBelow bits rng2
    let (noise, rng4) := pickPldiqNoiseValue rng3
    (mkPldiqProxyCase s!"fuzz/fail/deep-stack/w-{bits}/a-{avail}" bits
      #[noise, .slice (mkPatternSlice avail 1)], rng4)
  else if shape = 8 then
    (mkPldiqProxyRawCase "fuzz/underflow/empty" #[], rng2)
  else if shape = 9 then
    (mkPldiqProxyRawCase s!"fuzz/underflow/one-item/bits-{bits}" #[intV bits], rng2)
  else if shape = 10 then
    (mkPldiqProxyRawCase s!"fuzz/type/top-bits-not-int/bits-{bits}" #[.slice (mkPatternSlice bits), .null], rng2)
  else if shape = 11 then
    (mkPldiqProxyRawCase s!"fuzz/type/top-slice-not-slice/bits-{bits}" #[.null, intV bits], rng2)
  else if shape = 12 then
    (mkPldiqProxyRawCase "fuzz/range/bits-too-large" #[.slice (mkPatternSlice 16), intV 258], rng2)
  else if shape = 13 then
    (mkPldiqProxyRawCase "fuzz/range/bits-negative" #[.slice (mkPatternSlice 16), intV (-1)], rng2)
  else if shape = 14 then
    let (avail, rng3) := pickPldiqAvailAtLeast 8 rng2
    let (x, rng4) := pickSignedForWidth 8 rng3
    let tail := (mkPatternSlice avail).readBits (avail - 8)
    (mkPldiqProxyRawCase "fuzz/gas/exact"
      #[.slice (mkSignedSlice 8 x tail), intV 8]
      #[.pushInt (.num pldiqProxySetGasExact), .tonEnvOp .setGasLimit, pldixqInstr], rng4)
  else if shape = 15 then
    let (avail, rng3) := pickPldiqAvailAtLeast 8 rng2
    let (x, rng4) := pickSignedForWidth 8 rng3
    let tail := (mkPatternSlice avail 1).readBits (avail - 8)
    (mkPldiqProxyRawCase "fuzz/gas/exact-minus-one"
      #[.slice (mkSignedSlice 8 x tail), intV 8]
      #[.pushInt (.num pldiqProxySetGasExactMinusOne), .tonEnvOp .setGasLimit, pldixqInstr], rng4)
  else if shape = 16 then
    let bits' := if bits = 256 then 255 else bits
    let (x, rng3) := pickSignedForWidth bits' rng2
    let avail := bits' + 1
    let tail : BitString := #[true]
    (mkPldiqProxyCase s!"fuzz/ok/near-boundary/w-{bits'}-a-{avail}" bits'
      #[.slice (mkSignedSlice bits' x tail)], rng3)
  else if shape = 17 then
    let bits' := if bits = 1 then 2 else bits
    let avail := bits' - 1
    (mkPldiqProxyCase s!"fuzz/fail/near-boundary/w-{bits'}-a-{avail}" bits'
      #[.slice (mkPatternSlice avail 0)], rng2)
  else if shape = 18 then
    (mkPldiqProxyRawCase "fuzz/error-order/range-before-slice-pop" #[.null, intV 300], rng2)
  else
    (mkPldiqProxyRawCase "fuzz/error-order/bits-type-before-slice-pop" #[.null, .null], rng2)

def suite : InstrSuite where
  id := pldiqId
  unit := #[
    { name := "unit/direct/quiet-success-pushes-signed-int-then-minus1-no-remainder"
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
            (runPldiqDirect bits #[.slice input])
            #[intV n, intV (-1)]

        let refsInput := mkSignedSlice 8 (-42) tailBits5 #[refLeafA, refLeafB]
        expectOkStack "ok/refs/w-8-n-neg42-r-2"
          (runPldiqDirect 8 #[.slice refsInput])
          #[intV (-42), intV (-1)]

        let deep := mkSignedSlice 16 (-12345) tailBits11
        expectOkStack "ok/deep-stack-preserve-below"
          (runPldiqDirect 16 #[.null, intV 33, .slice deep])
          #[.null, intV 33, intV (-12345), intV (-1)]

        let partialCell : Cell := Cell.mkOrdinary (alternatingBits 48 1) #[refLeafA, refLeafB]
        let partialSlice : Slice := { cell := partialCell, bitPos := 9, refPos := 1 }
        let expected := expectedSignedFromSlice partialSlice 12
        expectOkStack "ok/partial-slice-cursor"
          (runPldiqDirect 12 #[.slice partialSlice])
          #[intV expected, intV (-1)] }
    ,
    { name := "unit/direct/quiet-failure-pushes-only-zero-in-prefetch-mode"
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
            (runPldiqDirect bits #[.slice input])
            #[intV 0]

        let refsInput := mkPatternSliceWithRefs 4 0 #[refLeafA, refLeafB]
        expectOkStack "fail/refs/w-5-a-4-r-2"
          (runPldiqDirect 5 #[.slice refsInput])
          #[intV 0]

        let deep := mkPatternSlice 10 1
        expectOkStack "fail/deep-stack-preserve-below"
          (runPldiqDirect 64 #[intV 77, .slice deep])
          #[intV 77, intV 0]

        let shortCursorCell : Cell := Cell.mkOrdinary (alternatingBits 24 0) #[refLeafA]
        let shortCursorSlice : Slice := { cell := shortCursorCell, bitPos := 20, refPos := 0 }
        expectOkStack "fail/partial-slice-short"
          (runPldiqDirect 5 #[.slice shortCursorSlice])
          #[intV 0]

        expectErr "nonquiet/short-throws-cellund"
          (runPldiqDirectInstr (.loadInt false true false 8) #[.slice (mkPatternSlice 7 0)]) .cellUnd }
    ,
    { name := "unit/direct/range-underflow-type-and-ordering"
      run := do
        expectErr "range/bits0-empty-stack"
          (runPldiqDirect 0 #[]) .rangeChk
        expectErr "range/bits0-top-not-slice"
          (runPldiqDirect 0 #[.null]) .rangeChk
        expectErr "range/bits0-valid-slice"
          (runPldiqDirect 0 #[.slice (mkPatternSlice 3 1)]) .rangeChk

        expectErr "underflow/empty"
          (runPldiqDirect 8 #[]) .stkUnd
        expectErr "type/top-null"
          (runPldiqDirect 8 #[.null]) .typeChk
        expectErr "type/top-int"
          (runPldiqDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell"
          (runPldiqDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/top-builder"
          (runPldiqDirect 8 #[.builder Builder.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPldiqDirect 8 #[.slice (mkPatternSlice 8 0), .null]) .typeChk
        expectErr "type/order-top-not-slice-over-short-slice"
          (runPldiqDirect 8 #[.slice (mkPatternSlice 0 1), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-family-fixed-vs-short-and-asm-gap"
      run := do
        let rawFamily := mkSliceFromBits
          (natToBits (loadIntWord24 false true true 1) 24 ++
           natToBits (loadIntWord24 false true true 17) 24 ++
           natToBits (loadIntWord24 false true true 256) 24 ++
           natToBits (loadIntWord24 true true true 5) 24 ++
           natToBits (loadIntWord24 false false true 5) 24 ++
           natToBits (loadIntWord24 false true false 5) 24 ++
           natToBits 0xd204 16 ++
           natToBits 0xa0 8)
        let r1 ← expectDecodeStep "decode/raw-pldiq-1" rawFamily (pldiqInstr 1) 24
        let r2 ← expectDecodeStep "decode/raw-pldiq-17" r1 (pldiqInstr 17) 24
        let r3 ← expectDecodeStep "decode/raw-pldiq-256" r2 (pldiqInstr 256) 24
        let r4 ← expectDecodeStep "decode/raw-plduq-5" r3 (.loadInt true true true 5) 24
        let r5 ← expectDecodeStep "decode/raw-ldiq-5" r4 (.loadInt false false true 5) 24
        let r6 ← expectDecodeStep "decode/raw-pldi-5" r5 (.loadInt false true false 5) 24
        let r7 ← expectDecodeStep "decode/raw-short-ldi-5" r6 (.loadInt false false false 5) 16
        let r8 ← expectDecodeStep "decode/raw-tail-add" r7 .add 8
        if r8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r8.bitsRemaining} bits remaining")

        match assembleCp0 [pldiqInstr 8] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"asm/pldiq-fixed: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "asm/pldiq-fixed: expected invOpcode, got success")

        let proxyCode ←
          match assembleCp0 [pldixqInstr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/proxy failed: {e}")
        let s0 := Slice.ofCell proxyCode
        let s1 ← expectDecodeStep "decode/proxy-pldixq" s0 pldixqInstr 16
        let s2 ← expectDecodeStep "decode/proxy-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/proxy-end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-loadint-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runPldiqDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/ldu-not-handled-here"
          (runPldiqDispatchFallback (.ldu 8) #[intV (-3)])
          #[intV (-3), intV dispatchSentinel]
        expectOkStack "dispatch/loadintvar-not-handled-here"
          (runPldiqDispatchFallback pldixqInstr #[intV 5])
          #[intV 5, intV dispatchSentinel] }
  ]
  oracle := #[
    mkPldiqProxyCase "ok/w-1-n-0-a-1" 1 #[.slice (mkSignedSlice 1 0)],
    mkPldiqProxyCase "ok/w-1-n-neg1-a-8" 1 #[.slice (mkSignedSlice 1 (-1) tailBits7)],
    mkPldiqProxyCase "ok/w-2-n-neg2-a-2" 2 #[.slice (mkSignedSlice 2 (-2))],
    mkPldiqProxyCase "ok/w-8-n-neg128-a-8" 8 #[.slice (mkSignedSlice 8 (-128))],
    mkPldiqProxyCase "ok/w-8-n-pos127-a-13" 8 #[.slice (mkSignedSlice 8 127 tailBits5)],
    mkPldiqProxyCase "ok/w-16-n-neg32768-a-16" 16 #[.slice (mkSignedSlice 16 (-32768))],
    mkPldiqProxyCase "ok/w-16-n-pos32767-a-23" 16 #[.slice (mkSignedSlice 16 32767 tailBits7)],
    mkPldiqProxyCase "ok/w-32-n-negmin-a-32" 32 #[.slice (mkSignedSlice 32 (-(intPow2 31)))],
    mkPldiqProxyCase "ok/w-64-n-posmax-a-64" 64 #[.slice (mkSignedSlice 64 (intPow2 63 - 1))],
    mkPldiqProxyCase "ok/w-127-n-negmin-a-127" 127 #[.slice (mkSignedSlice 127 (-(intPow2 126)))],
    mkPldiqProxyCase "ok/w-128-n-posmax-a-133" 128 #[.slice (mkSignedSlice 128 (intPow2 127 - 1) tailBits5)],
    mkPldiqProxyCase "ok/w-201-sample-pos-a-201" 201 #[.slice (mkSignedSlice 201 sampleWidePos201)],
    mkPldiqProxyCase "ok/w-201-sample-neg-a-208" 201 #[.slice (mkSignedSlice 201 sampleWideNeg201 tailBits7)],
    mkPldiqProxyCase "ok/w-255-near-max-a-255" 255 #[.slice (mkSignedSlice 255 (intPow2 254 - 7))],
    mkPldiqProxyCase "ok/w-256-min-a-256" 256 #[.slice (mkSignedSlice 256 (-(intPow2 255)))],
    mkPldiqProxyCase "ok/w-256-max-a-259" 256 #[.slice (mkSignedSlice 256 (intPow2 255 - 1) tailBits3)],
    mkPldiqProxyCase "ok/deep-stack/w-16-n-neg5-a-23" 16 #[.null, intV 42, .slice (mkSignedSlice 16 (-5) tailBits7)],
    mkPldiqProxyCase "ok/refs/w-8-n-neg42-a-13-r-2" 8
      #[.slice (mkSignedSlice 8 (-42) tailBits5 #[refLeafA, refLeafB])],

    mkPldiqProxyCase "fail/w-1-a-0" 1 #[.slice (mkPatternSlice 0 0)],
    mkPldiqProxyCase "fail/w-2-a-1" 2 #[.slice (mkPatternSlice 1 1)],
    mkPldiqProxyCase "fail/w-8-a-7" 8 #[.slice (mkPatternSlice 7 0)],
    mkPldiqProxyCase "fail/w-16-a-0" 16 #[.slice (mkPatternSlice 0 1)],
    mkPldiqProxyCase "fail/w-64-a-63" 64 #[.slice (mkPatternSlice 63 0)],
    mkPldiqProxyCase "fail/w-128-a-127" 128 #[.slice (mkPatternSlice 127 1)],
    mkPldiqProxyCase "fail/w-256-a-255" 256 #[.slice (mkPatternSlice 255 0)],
    mkPldiqProxyCase "fail/deep-stack/w-64-a-10" 64 #[intV 33, .slice (mkPatternSlice 10 1)],
    mkPldiqProxyCase "fail/refs/w-5-a-4-r-1" 5 #[.slice (mkPatternSliceWithRefs 4 0 #[refLeafA])],
    mkPldiqProxyCase "fail/refs/w-256-a-128-r-2" 256
      #[.slice (mkPatternSliceWithRefs 128 1 #[refLeafA, refLeafB])],

    mkPldiqProxyRawCase "underflow/empty" #[],
    mkPldiqProxyRawCase "underflow/one-item" #[intV 8],
    mkPldiqProxyRawCase "type/top-bits-not-int" #[.slice (mkPatternSlice 8 0), .null],
    mkPldiqProxyRawCase "type/top-slice-not-slice" #[.null, intV 8],
    mkPldiqProxyRawCase "range/bits-too-large" #[.slice (mkPatternSlice 16 1), intV 258],
    mkPldiqProxyRawCase "range/bits-negative" #[.slice (mkPatternSlice 16 0), intV (-1)],
    mkPldiqProxyRawCase "error-order/range-before-slice-pop" #[.null, intV 300],
    mkPldiqProxyRawCase "error-order/bits-type-before-slice-pop" #[.null, .null],

    mkPldiqProxyRawCase "gas/exact-cost-succeeds"
      #[.slice (mkSignedSlice 8 (-5) tailBits11), intV 8]
      #[.pushInt (.num pldiqProxySetGasExact), .tonEnvOp .setGasLimit, pldixqInstr],
    mkPldiqProxyRawCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkSignedSlice 8 7 tailBits11), intV 8]
      #[.pushInt (.num pldiqProxySetGasExactMinusOne), .tonEnvOp .setGasLimit, pldixqInstr]
  ]
  fuzz := #[
    { seed := 2026021055
      count := 320
      gen := genPldiqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDIQ
