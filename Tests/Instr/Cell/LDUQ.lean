import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDUQ

/-
LDUQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadInt.lean`
    (`.loadInt true false true bits`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.loadInt _ _ _ _ => .invOpcode`, var-form `.loadIntVar` is encodable)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xd708>>3` fixed-width decode family for `{P}LD{I,U}{Q} <bits>`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_int_fixed2` → `exec_load_int_common`, mode args `5` for `LDUQ`).

Quiet fixed-width contract (non-prefetch + unsigned + quiet `LDUQ`) aligned to C++:
- success (`have(bits)`): push loaded unsigned int, then remainder slice, then `-1`;
- failure (`!have(bits)`): no exception, push original slice, then `0`;
- underflow/type failures happen when popping the source slice (after `bits==0` check);
- `bits==0` raises `rangeChk` before stack access.

Current Lean opcode-assembly mismatch:
- `decodeCp0` recognizes fixed-width `LDUQ` opcodes via `0xd708>>3`;
- `assembleCp0` currently rejects `.loadInt ...` with `.invOpcode`.
To keep oracle/fuzz coverage executable, this suite uses an oracle proxy program
(`LDUXQ` with explicit `bits` on stack), which executes the same C++ common load path.
-/

private def lduqId : InstrId := { name := "LDUQ" }

private def dispatchSentinel : Int := 911

private def lduqInstr (bits : Nat) : Instr :=
  .loadInt true false true bits

private def lduxqInstr : Instr :=
  .loadIntVar true false true

private def lduqProxyGasInstr : Instr :=
  lduxqInstr

private def mkLduqProxyCase
    (name : String)
    (bits : Nat)
    (stackNoBits : Array Value)
    (program : Array Instr := #[lduxqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lduqId
    program := program
    initStack := stackNoBits.push (intV bits)
    gasLimits := gasLimits
    fuel := fuel }

private def mkLduqProxyRawCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lduxqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lduqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLduqDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt (lduqInstr bits) stack

private def runLduqDirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt instr stack

private def runLduqDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadInt instr (VM.push (intV dispatchSentinel)) stack

private def lduqProxySetGasExact : Int :=
  computeExactGasBudget lduqProxyGasInstr

private def lduqProxySetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lduqProxyGasInstr

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

private def expectedUnsignedFromSlice (s : Slice) (bits : Nat) : Int :=
  Int.ofNat (bitsToNat (s.readBits bits))

private def loadIntWord24 (unsigned prefetch quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat := (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := 0xd708 >>> 3
  (prefix13 <<< 11) + args11

private def loadIntVarWord (unsigned prefetch quiet : Bool) : Nat :=
  let args3 : Nat := (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  0xd700 + args3

private def lduqWidthBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickLduqWidthBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (lduqWidthBoundaryPool.size - 1)
  (lduqWidthBoundaryPool[idx]!, rng')

private def pickLduqWidthMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickLduqWidthBoundary rng1
  else
    randNat rng1 1 256

private def pickLduqAvailAtLeast (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let maxExtra : Nat := Nat.min 64 (1023 - bits)
  let (extra, rng1) := randNat rng0 0 maxExtra
  (bits + extra, rng1)

private def pickLduqAvailBelow (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    randNat rng0 0 (bits - 1)

private def pickLduqRefPackNonEmpty (rng0 : StdGen) : Array Cell × StdGen :=
  let (pick, rng1) := randNat rng0 0 1
  if pick = 0 then
    (#[refLeafA], rng1)
  else
    (#[refLeafA, refLeafB], rng1)

private def pickLduqNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 19
    else .cell Cell.empty
  (v, rng1)

private def genLduqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (bits, rng2) := pickLduqWidthMixed rng1
  if shape = 0 then
    (mkLduqProxyCase s!"fuzz/ok/exact/w-{bits}" bits #[.slice (mkPatternSlice bits)], rng2)
  else if shape = 1 then
    let (avail, rng3) := pickLduqAvailAtLeast bits rng2
    (mkLduqProxyCase s!"fuzz/ok/extra/w-{bits}-a-{avail}" bits #[.slice (mkPatternSlice avail)], rng3)
  else if shape = 2 then
    let (avail, rng3) := pickLduqAvailAtLeast bits rng2
    let (refs, rng4) := pickLduqRefPackNonEmpty rng3
    (mkLduqProxyCase s!"fuzz/ok/refs/w-{bits}-a-{avail}-r-{refs.size}" bits
      #[.slice (mkPatternSliceWithRefs avail 0 refs)], rng4)
  else if shape = 3 then
    let (avail, rng3) := pickLduqAvailAtLeast bits rng2
    let (noise, rng4) := pickLduqNoiseValue rng3
    (mkLduqProxyCase s!"fuzz/ok/deep-stack/w-{bits}-a-{avail}" bits
      #[noise, .slice (mkPatternSlice avail)], rng4)
  else if shape = 4 then
    let (avail, rng3) := pickLduqAvailBelow bits rng2
    (mkLduqProxyCase s!"fuzz/fail/short/w-{bits}-a-{avail}" bits #[.slice (mkPatternSlice avail)], rng3)
  else if shape = 5 then
    let (avail, rng3) := pickLduqAvailBelow bits rng2
    let (refs, rng4) := pickLduqRefPackNonEmpty rng3
    (mkLduqProxyCase s!"fuzz/fail/short-refs/w-{bits}-a-{avail}-r-{refs.size}" bits
      #[.slice (mkPatternSliceWithRefs avail 1 refs)], rng4)
  else if shape = 6 then
    let (avail, rng3) := pickLduqAvailBelow bits rng2
    let (noise, rng4) := pickLduqNoiseValue rng3
    (mkLduqProxyCase s!"fuzz/fail/deep-stack/w-{bits}-a-{avail}" bits
      #[noise, .slice (mkPatternSlice avail 1)], rng4)
  else if shape = 7 then
    (mkLduqProxyRawCase "fuzz/underflow/empty" #[], rng2)
  else if shape = 8 then
    (mkLduqProxyRawCase s!"fuzz/underflow/one-item/bits-{bits}" #[intV bits], rng2)
  else if shape = 9 then
    (mkLduqProxyRawCase s!"fuzz/type/top-bits-not-int/bits-{bits}" #[.slice (mkPatternSlice bits), .null], rng2)
  else if shape = 10 then
    (mkLduqProxyRawCase s!"fuzz/type/top-slice-not-slice/bits-{bits}" #[.null, intV bits], rng2)
  else if shape = 11 then
    (mkLduqProxyRawCase "fuzz/range/bits-too-large" #[.slice (mkPatternSlice 16), intV 257], rng2)
  else if shape = 12 then
    (mkLduqProxyRawCase "fuzz/range/bits-negative" #[.slice (mkPatternSlice 16), intV (-1)], rng2)
  else if shape = 13 then
    let (avail, rng3) := pickLduqAvailAtLeast 8 rng2
    (mkLduqProxyRawCase "fuzz/gas/exact"
      #[.slice (mkPatternSlice avail), intV 8]
      #[.pushInt (.num lduqProxySetGasExact), .tonEnvOp .setGasLimit, lduxqInstr], rng3)
  else if shape = 14 then
    let (avail, rng3) := pickLduqAvailAtLeast 8 rng2
    (mkLduqProxyRawCase "fuzz/gas/exact-minus-one"
      #[.slice (mkPatternSlice avail), intV 8]
      #[.pushInt (.num lduqProxySetGasExactMinusOne), .tonEnvOp .setGasLimit, lduxqInstr], rng3)
  else if shape = 15 then
    let bits' := if bits = 256 then 255 else bits
    let avail := bits' + 1
    (mkLduqProxyCase s!"fuzz/ok/near-boundary/w-{bits'}-a-{avail}" bits'
      #[.slice (mkPatternSlice avail)], rng2)
  else if shape = 16 then
    let bits' := if bits = 1 then 2 else bits
    let avail := bits' - 1
    (mkLduqProxyCase s!"fuzz/fail/near-boundary/w-{bits'}-a-{avail}" bits'
      #[.slice (mkPatternSlice avail)], rng2)
  else if shape = 17 then
    let (avail, rng3) := pickLduqAvailAtLeast bits rng2
    (mkLduqProxyRawCase s!"fuzz/ok/raw-proxy/w-{bits}-a-{avail}"
      #[.slice (mkPatternSlice avail), intV bits] #[lduxqInstr], rng3)
  else
    let (avail, rng3) := pickLduqAvailAtLeast 8 rng2
    (mkLduqProxyRawCase "fuzz/range/bits-nan"
      #[.slice (mkPatternSlice avail)]
      #[.pushInt .nan, lduxqInstr], rng3)

def suite : InstrSuite where
  id := lduqId
  unit := #[
    { name := "unit/direct/quiet-success-pushes-int-remainder-and-minus1"
      run := do
        let checks : Array (Nat × Nat) :=
          #[
            (1, 1),
            (1, 5),
            (2, 2),
            (7, 11),
            (8, 8),
            (16, 20),
            (64, 80),
            (127, 140),
            (256, 256)
          ]
        for c in checks do
          let bits := c.1
          let avail := c.2
          let input := mkPatternSlice avail
          let expected := expectedUnsignedFromSlice input bits
          let rem := input.advanceBits bits
          expectOkStack s!"ok/w-{bits}-a-{avail}"
            (runLduqDirect bits #[.slice input])
            #[intV expected, .slice rem, intV (-1)]

        let refsInput := mkPatternSliceWithRefs 12 1 #[refLeafA, refLeafB]
        let refsExpected := expectedUnsignedFromSlice refsInput 9
        let refsRem := refsInput.advanceBits 9
        expectOkStack "ok/refs/w-9-a-12-r-2"
          (runLduqDirect 9 #[.slice refsInput])
          #[intV refsExpected, .slice refsRem, intV (-1)]

        let deep := mkPatternSlice 14 1
        let deepExpected := expectedUnsignedFromSlice deep 9
        let deepRem := deep.advanceBits 9
        expectOkStack "ok/deep-stack-preserve-below"
          (runLduqDirect 9 #[.null, intV 33, .slice deep])
          #[.null, intV 33, intV deepExpected, .slice deepRem, intV (-1)] }
    ,
    { name := "unit/direct/quiet-failure-preserves-original-slice-and-status0"
      run := do
        let checks : Array (Nat × Nat) :=
          #[
            (1, 0),
            (2, 1),
            (8, 7),
            (16, 0),
            (64, 63),
            (128, 127),
            (256, 255)
          ]
        for c in checks do
          let bits := c.1
          let avail := c.2
          let input := mkPatternSlice avail
          expectOkStack s!"fail/w-{bits}-a-{avail}"
            (runLduqDirect bits #[.slice input])
            #[.slice input, intV 0]

        let refsInput := mkPatternSliceWithRefs 4 1 #[refLeafA, refLeafB]
        expectOkStack "fail/refs/w-5-a-4-r-2"
          (runLduqDirect 5 #[.slice refsInput])
          #[.slice refsInput, intV 0]

        let deep := mkPatternSlice 10
        expectOkStack "fail/deep-stack-preserve-below"
          (runLduqDirect 64 #[intV 77, .slice deep])
          #[intV 77, .slice deep, intV 0]

        expectErr "nonquiet/short-throws-cellund"
          (runLduqDirectInstr (.loadInt true false false 8) #[.slice (mkPatternSlice 7)]) .cellUnd }
    ,
    { name := "unit/direct/range-underflow-type-and-error-order"
      run := do
        expectErr "range/bits0-before-underflow"
          (runLduqDirect 0 #[]) .rangeChk
        expectErr "range/bits0-before-type"
          (runLduqDirect 0 #[.null]) .rangeChk
        expectErr "range/bits0-before-cellund"
          (runLduqDirect 0 #[.slice (mkPatternSlice 0)]) .rangeChk

        expectErr "underflow/empty"
          (runLduqDirect 8 #[]) .stkUnd
        expectErr "type/top-null"
          (runLduqDirect 8 #[.null]) .typeChk
        expectErr "type/top-int"
          (runLduqDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell"
          (runLduqDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLduqDirect 8 #[.slice (mkPatternSlice 9), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-boundaries-and-assembler-gap"
      run := do
        let rawFamily := mkSliceFromBits
          (natToBits (loadIntVarWord true false true) 16 ++
           natToBits (loadIntVarWord true true true) 16 ++
           natToBits (loadIntWord24 true false true 1) 24 ++
           natToBits (loadIntWord24 true false true 17) 24 ++
           natToBits (loadIntWord24 true false true 256) 24 ++
           natToBits (loadIntWord24 false false true 5) 24 ++
           natToBits (loadIntWord24 true true true 5) 24 ++
           natToBits (loadIntWord24 true false false 5) 24 ++
           natToBits 0xd304 16 ++
           natToBits 0xd710 16 ++
           natToBits 0xa0 8)
        let r1 ← expectDecodeStep "decode/raw-lduxq" rawFamily lduxqInstr 16
        let r2 ← expectDecodeStep "decode/raw-plduxq-neighbor" r1 (.loadIntVar true true true) 16
        let r3 ← expectDecodeStep "decode/raw-lduq-1" r2 (lduqInstr 1) 24
        let r4 ← expectDecodeStep "decode/raw-lduq-17" r3 (lduqInstr 17) 24
        let r5 ← expectDecodeStep "decode/raw-lduq-256" r4 (lduqInstr 256) 24
        let r6 ← expectDecodeStep "decode/raw-ldiq-5" r5 (.loadInt false false true 5) 24
        let r7 ← expectDecodeStep "decode/raw-plduq-5" r6 (.loadInt true true true 5) 24
        let r8 ← expectDecodeStep "decode/raw-ldu-5" r7 (.loadInt true false false 5) 24
        let r9 ← expectDecodeStep "decode/raw-short-ldu-5" r8 (.ldu 5) 16
        let r10 ← expectDecodeStep "decode/raw-boundary-plduz-0" r9 (.cellExt (.plduz 0)) 16
        let r11 ← expectDecodeStep "decode/raw-tail-add" r10 .add 8
        if r11.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r11.bitsRemaining} bits remaining")

        match assembleCp0 [lduqInstr 8] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"asm/lduq-fixed-8: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "asm/lduq-fixed-8: expected invOpcode, got success")

        match assembleCp0 [lduqInstr 0] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"asm/lduq-fixed-0: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "asm/lduq-fixed-0: expected invOpcode, got success")

        let proxySingle ←
          match assembleCp0 [lduxqInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/proxy-single failed: {e}")
        if proxySingle.bits = natToBits (loadIntVarWord true false true) 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/lduxq: expected 0xd705 encoding, got bits {proxySingle.bits}")

        let proxyCode ←
          match assembleCp0 [lduxqInstr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/proxy failed: {e}")
        let s0 := Slice.ofCell proxyCode
        let s1 ← expectDecodeStep "decode/proxy-lduxq" s0 lduxqInstr 16
        let s2 ← expectDecodeStep "decode/proxy-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/proxy-end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-loadint-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runLduqDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/ldu-short-not-handled-here"
          (runLduqDispatchFallback (.ldu 8) #[intV (-3)])
          #[intV (-3), intV dispatchSentinel]
        expectOkStack "dispatch/loadintvar-not-handled-here"
          (runLduqDispatchFallback lduxqInstr #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/loadslice-neighbor-not-handled-here"
          (runLduqDispatchFallback (.loadSliceFixed false true 8) #[.cell Cell.empty])
          #[.cell Cell.empty, intV dispatchSentinel] }
  ]
  oracle := #[
    mkLduqProxyCase "ok/w-1-a-1" 1 #[.slice (mkPatternSlice 1)],
    mkLduqProxyCase "ok/w-1-a-5" 1 #[.slice (mkPatternSlice 5)],
    mkLduqProxyCase "ok/w-2-a-2" 2 #[.slice (mkPatternSlice 2)],
    mkLduqProxyCase "ok/w-7-a-11" 7 #[.slice (mkPatternSlice 11)],
    mkLduqProxyCase "ok/w-8-a-8" 8 #[.slice (mkPatternSlice 8)],
    mkLduqProxyCase "ok/w-16-a-20" 16 #[.slice (mkPatternSlice 20)],
    mkLduqProxyCase "ok/w-31-a-63" 31 #[.slice (mkPatternSlice 63)],
    mkLduqProxyCase "ok/w-64-a-64" 64 #[.slice (mkPatternSlice 64)],
    mkLduqProxyCase "ok/w-127-a-140" 127 #[.slice (mkPatternSlice 140)],
    mkLduqProxyCase "ok/w-128-a-256" 128 #[.slice (mkPatternSlice 256)],
    mkLduqProxyCase "ok/w-255-a-255" 255 #[.slice (mkPatternSlice 255)],
    mkLduqProxyCase "ok/w-256-a-256" 256 #[.slice (mkPatternSlice 256)],
    mkLduqProxyCase "ok/deep-stack-null-below" 9 #[.null, .slice (mkPatternSlice 14 1)],
    mkLduqProxyCase "ok/deep-stack-two-below" 5 #[intV (-7), .null, .slice (mkPatternSlice 9)],
    mkLduqProxyCase "ok/refs/w-9-a-12-r-2" 9 #[.slice (mkPatternSliceWithRefs 12 1 #[refLeafA, refLeafB])],
    mkLduqProxyCase "ok/refs/w-256-a-256-r-1" 256 #[.slice (mkPatternSliceWithRefs 256 0 #[refLeafA])],

    mkLduqProxyCase "fail/w-1-a-0" 1 #[.slice (mkPatternSlice 0)],
    mkLduqProxyCase "fail/w-2-a-1" 2 #[.slice (mkPatternSlice 1)],
    mkLduqProxyCase "fail/w-8-a-7" 8 #[.slice (mkPatternSlice 7)],
    mkLduqProxyCase "fail/w-16-a-0" 16 #[.slice (mkPatternSlice 0)],
    mkLduqProxyCase "fail/w-64-a-63" 64 #[.slice (mkPatternSlice 63)],
    mkLduqProxyCase "fail/w-128-a-127" 128 #[.slice (mkPatternSlice 127)],
    mkLduqProxyCase "fail/w-256-a-255" 256 #[.slice (mkPatternSlice 255)],
    mkLduqProxyCase "fail/deep-stack/w-64-a-10" 64 #[intV 33, .slice (mkPatternSlice 10)],
    mkLduqProxyCase "fail/refs/w-5-a-4-r-1" 5 #[.slice (mkPatternSliceWithRefs 4 1 #[refLeafA])],
    mkLduqProxyCase "fail/refs/w-256-a-128-r-2" 256 #[.slice (mkPatternSliceWithRefs 128 0 #[refLeafA, refLeafB])],

    mkLduqProxyRawCase "underflow/empty" #[],
    mkLduqProxyRawCase "underflow/one-item" #[intV 8],
    mkLduqProxyRawCase "type/top-bits-not-int" #[.slice (mkPatternSlice 8), .null],
    mkLduqProxyRawCase "type/top-slice-not-slice" #[.null, intV 8],
    mkLduqProxyRawCase "range/bits-too-large" #[.slice (mkPatternSlice 16), intV 257],
    mkLduqProxyRawCase "range/bits-negative" #[.slice (mkPatternSlice 16), intV (-1)],

    mkLduqProxyRawCase "gas/exact-cost-succeeds"
      #[.slice (mkPatternSlice 14), intV 8]
      #[.pushInt (.num lduqProxySetGasExact), .tonEnvOp .setGasLimit, lduxqInstr],
    mkLduqProxyRawCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkPatternSlice 14), intV 8]
      #[.pushInt (.num lduqProxySetGasExactMinusOne), .tonEnvOp .setGasLimit, lduxqInstr]
  ]
  fuzz := #[
    { seed := 2026021061
      count := 320
      gen := genLduqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDUQ
