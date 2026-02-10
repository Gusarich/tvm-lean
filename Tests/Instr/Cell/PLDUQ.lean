import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDUQ

/-
PLDUQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadInt.lean` (`.loadInt unsigned=true prefetch=true quiet=true bits`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.loadInt _ _ _ _ => .invOpcode`, `.loadIntVar` encodable)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd708>>3` decode family for fixed `{P}LD{I,U}{Q} <bits>`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_int_fixed2` → `exec_load_int_common`, mode args `7` for `PLDUQ`).

Quiet fixed-width contract (prefetch + unsigned + quiet `PLDUQ`) verified against C++:
- success (`have(bits)`): push loaded unsigned int, then `-1`; no remainder slice in prefetch mode;
- failure (`!have(bits)`): no exception, push only `0` (no slice re-push in prefetch mode);
- underflow/type failures happen at the initial slice pop, before quiet status behavior.

Current Lean opcode-assembly mismatch:
- `decodeCp0` recognizes fixed-width `PLDUQ` opcodes via `0xd708>>3`;
- `assembleCp0` currently rejects `.loadInt ...` with `.invOpcode`.
To keep oracle/fuzz coverage executable, this suite uses an oracle proxy program
(`LDUXQ` with explicit `bits` on stack), which exercises the same C++ common load path.
-/

private def plduqId : InstrId := { name := "PLDUQ" }

private def plduqInstr (bits : Nat) : Instr :=
  .loadInt true true true bits

private def plduxqInstr : Instr :=
  .loadIntVar true true true

private def plduqProxyGasInstr : Instr :=
  plduxqInstr

private def mkPlduqProxyCase
    (name : String)
    (bits : Nat)
    (stackNoBits : Array Value)
    (program : Array Instr := #[plduxqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := plduqId
    program := program
    initStack := stackNoBits.push (intV bits)
    gasLimits := gasLimits
    fuel := fuel }

private def mkPlduqProxyRawCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[plduxqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := plduqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPlduqDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt (plduqInstr bits) stack

private def runPlduqDirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadInt instr stack

private def runPlduqDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadInt instr (VM.push (intV 917)) stack

private def plduqProxySetGasExact : Int :=
  computeExactGasBudget plduqProxyGasInstr

private def plduqProxySetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne plduqProxyGasInstr

private def alternatingBits (n : Nat) : BitString :=
  Array.ofFn (n := n) fun i => i.1 % 2 = 0

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3)

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 13 4)

private def mkSliceWithRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkPatternSlice (n : Nat) : Slice :=
  mkSliceFromBits (alternatingBits n)

private def mkPatternSliceWithRefs (n : Nat) (refs : Array Cell := #[refLeafA]) : Slice :=
  mkSliceWithRefs (alternatingBits n) refs

private def expectedUnsignedFromSlice (s : Slice) (bits : Nat) : Int :=
  Int.ofNat (bitsToNat (s.readBits bits))

private def loadIntWord24 (unsigned prefetch quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat := (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := 0xd708 >>> 3
  (prefix13 <<< 11) + args11

private def plduqWidthBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickPlduqWidthBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (plduqWidthBoundaryPool.size - 1)
  (plduqWidthBoundaryPool[idx]!, rng')

private def pickPlduqWidthMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickPlduqWidthBoundary rng1
  else
    randNat rng1 1 256

private def pickPlduqAvailAtLeast (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let maxExtra : Nat := Nat.min 64 (1023 - bits)
  let (extra, rng1) := randNat rng0 0 maxExtra
  (bits + extra, rng1)

private def pickPlduqAvailBelow (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    randNat rng0 0 (bits - 1)

private def pickPlduqRefPackNonEmpty (rng0 : StdGen) : Array Cell × StdGen :=
  let (pick, rng1) := randNat rng0 0 1
  if pick = 0 then
    (#[refLeafA], rng1)
  else
    (#[refLeafA, refLeafB], rng1)

private def pickPlduqNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 19
    else .cell Cell.empty
  (v, rng1)

private def genPlduqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (bits, rng2) := pickPlduqWidthMixed rng1
  if shape = 0 then
    (mkPlduqProxyCase s!"fuzz/ok/exact/w-{bits}" bits #[.slice (mkPatternSlice bits)], rng2)
  else if shape = 1 then
    let (avail, rng3) := pickPlduqAvailAtLeast bits rng2
    (mkPlduqProxyCase s!"fuzz/ok/extra/w-{bits}-a-{avail}" bits #[.slice (mkPatternSlice avail)], rng3)
  else if shape = 2 then
    let (avail, rng3) := pickPlduqAvailAtLeast bits rng2
    let (refs, rng4) := pickPlduqRefPackNonEmpty rng3
    (mkPlduqProxyCase s!"fuzz/ok/refs/w-{bits}-a-{avail}-r-{refs.size}" bits
      #[.slice (mkPatternSliceWithRefs avail refs)], rng4)
  else if shape = 3 then
    let (avail, rng3) := pickPlduqAvailAtLeast bits rng2
    let (noise, rng4) := pickPlduqNoiseValue rng3
    (mkPlduqProxyCase s!"fuzz/ok/deep-stack/w-{bits}-a-{avail}" bits
      #[noise, .slice (mkPatternSlice avail)], rng4)
  else if shape = 4 then
    let (avail, rng3) := pickPlduqAvailBelow bits rng2
    (mkPlduqProxyCase s!"fuzz/fail/short/w-{bits}-a-{avail}" bits #[.slice (mkPatternSlice avail)], rng3)
  else if shape = 5 then
    let (avail, rng3) := pickPlduqAvailBelow bits rng2
    let (refs, rng4) := pickPlduqRefPackNonEmpty rng3
    (mkPlduqProxyCase s!"fuzz/fail/short-refs/w-{bits}-a-{avail}-r-{refs.size}" bits
      #[.slice (mkPatternSliceWithRefs avail refs)], rng4)
  else if shape = 6 then
    let (avail, rng3) := pickPlduqAvailBelow bits rng2
    let (noise, rng4) := pickPlduqNoiseValue rng3
    (mkPlduqProxyCase s!"fuzz/fail/deep-stack/w-{bits}-a-{avail}" bits
      #[noise, .slice (mkPatternSlice avail)], rng4)
  else if shape = 7 then
    (mkPlduqProxyRawCase "fuzz/underflow/empty" #[], rng2)
  else if shape = 8 then
    (mkPlduqProxyRawCase s!"fuzz/underflow/one-item/bits-{bits}" #[intV bits], rng2)
  else if shape = 9 then
    (mkPlduqProxyRawCase s!"fuzz/type/top-bits-not-int/bits-{bits}" #[.slice (mkPatternSlice bits), .null], rng2)
  else if shape = 10 then
    (mkPlduqProxyRawCase s!"fuzz/type/top-slice-not-slice/bits-{bits}" #[.null, intV bits], rng2)
  else if shape = 11 then
    (mkPlduqProxyRawCase "fuzz/range/bits-too-large" #[.slice (mkPatternSlice 16), intV 257], rng2)
  else if shape = 12 then
    (mkPlduqProxyRawCase "fuzz/range/bits-negative" #[.slice (mkPatternSlice 16), intV (-1)], rng2)
  else if shape = 13 then
    let (avail, rng3) := pickPlduqAvailAtLeast 8 rng2
    (mkPlduqProxyRawCase "fuzz/gas/exact"
      #[.slice (mkPatternSlice avail), intV 8]
      #[.pushInt (.num plduqProxySetGasExact), .tonEnvOp .setGasLimit, plduxqInstr], rng3)
  else if shape = 14 then
    let (avail, rng3) := pickPlduqAvailAtLeast 8 rng2
    (mkPlduqProxyRawCase "fuzz/gas/exact-minus-one"
      #[.slice (mkPatternSlice avail), intV 8]
      #[.pushInt (.num plduqProxySetGasExactMinusOne), .tonEnvOp .setGasLimit, plduxqInstr], rng3)
  else if shape = 15 then
    let bits' := if bits = 256 then 255 else bits
    let avail := bits' + 1
    (mkPlduqProxyCase s!"fuzz/ok/near-boundary/w-{bits'}-a-{avail}" bits'
      #[.slice (mkPatternSlice avail)], rng2)
  else if shape = 16 then
    let bits' := if bits = 1 then 2 else bits
    let avail := bits' - 1
    (mkPlduqProxyCase s!"fuzz/fail/near-boundary/w-{bits'}-a-{avail}" bits'
      #[.slice (mkPatternSlice avail)], rng2)
  else
    let (avail, rng3) := pickPlduqAvailAtLeast bits rng2
    (mkPlduqProxyRawCase s!"fuzz/ok/raw-proxy/w-{bits}-a-{avail}"
      #[.slice (mkPatternSlice avail), intV bits]
      #[plduxqInstr], rng3)

def suite : InstrSuite where
  id := plduqId
  unit := #[
    { name := "unit/direct/quiet-success-pushes-int-then-minus1-no-remainder"
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
          expectOkStack s!"ok/w-{bits}-a-{avail}"
            (runPlduqDirect bits #[.slice input])
            #[intV expected, intV (-1)]

        let refsInput := mkPatternSliceWithRefs 12 #[refLeafA, refLeafB]
        let refsExpected := expectedUnsignedFromSlice refsInput 9
        expectOkStack "ok/refs/w-9-a-12-r-2"
          (runPlduqDirect 9 #[.slice refsInput])
          #[intV refsExpected, intV (-1)]

        let deep := mkPatternSlice 14
        let deepExpected := expectedUnsignedFromSlice deep 9
        expectOkStack "ok/deep-stack-preserve-below"
          (runPlduqDirect 9 #[.null, intV 33, .slice deep])
          #[.null, intV 33, intV deepExpected, intV (-1)] }
    ,
    { name := "unit/direct/quiet-failure-pushes-only-zero"
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
            (runPlduqDirect bits #[.slice input])
            #[intV 0]

        let refsInput := mkPatternSliceWithRefs 4 #[refLeafA, refLeafB]
        expectOkStack "fail/refs/w-5-a-4-r-2"
          (runPlduqDirect 5 #[.slice refsInput])
          #[intV 0]

        let deep := mkPatternSlice 10
        expectOkStack "fail/deep-stack-preserve-below"
          (runPlduqDirect 64 #[intV 77, .slice deep])
          #[intV 77, intV 0]

        expectErr "nonquiet/short-throws-cellund"
          (runPlduqDirectInstr (.loadInt true true false 8) #[.slice (mkPatternSlice 7)]) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-and-ordering"
      run := do
        expectErr "underflow/empty" (runPlduqDirect 8 #[]) .stkUnd
        expectErr "type/top-null" (runPlduqDirect 8 #[.null]) .typeChk
        expectErr "type/top-int" (runPlduqDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell" (runPlduqDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPlduqDirect 8 #[.slice (mkPatternSlice 9), .null]) .typeChk

        expectErr "range/bits0-before-underflow"
          (runPlduqDirect 0 #[]) .rangeChk
        expectErr "range/bits0-before-type"
          (runPlduqDirect 0 #[.null]) .rangeChk }
    ,
    { name := "unit/opcode/decode-family-fixed-vs-short-and-asm-gap"
      run := do
        let rawFamily := mkSliceFromBits
          (natToBits (loadIntWord24 true true true 1) 24 ++
           natToBits (loadIntWord24 true true true 17) 24 ++
           natToBits (loadIntWord24 true true true 256) 24 ++
           natToBits (loadIntWord24 false true true 5) 24 ++
           natToBits (loadIntWord24 true false true 5) 24 ++
           natToBits (loadIntWord24 true true false 5) 24 ++
           natToBits 0xd304 16 ++
           natToBits 0xa0 8)
        let r1 ← expectDecodeStep "decode/raw-plduq-1" rawFamily (plduqInstr 1) 24
        let r2 ← expectDecodeStep "decode/raw-plduq-17" r1 (plduqInstr 17) 24
        let r3 ← expectDecodeStep "decode/raw-plduq-256" r2 (plduqInstr 256) 24
        let r4 ← expectDecodeStep "decode/raw-pldiq-5" r3 (.loadInt false true true 5) 24
        let r5 ← expectDecodeStep "decode/raw-lduq-5" r4 (.loadInt true false true 5) 24
        let r6 ← expectDecodeStep "decode/raw-pldu-5" r5 (.loadInt true true false 5) 24
        let r7 ← expectDecodeStep "decode/raw-short-ldu-5" r6 (.ldu 5) 16
        let r8 ← expectDecodeStep "decode/raw-tail-add" r7 .add 8
        if r8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r8.bitsRemaining} bits remaining")

        match assembleCp0 [plduqInstr 8] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"asm/plduq-fixed: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "asm/plduq-fixed: expected invOpcode, got success")

        let proxyCode ←
          match assembleCp0 [plduxqInstr, .add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/proxy failed: {e}")
        let s0 := Slice.ofCell proxyCode
        let s1 ← expectDecodeStep "decode/proxy-plduxq" s0 plduxqInstr 16
        let s2 ← expectDecodeStep "decode/proxy-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/proxy-end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-loadint-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runPlduqDispatchFallback .add #[.null])
          #[.null, intV 917]
        expectOkStack "dispatch/ldu-not-handled-here"
          (runPlduqDispatchFallback (.ldu 8) #[intV (-3)])
          #[intV (-3), intV 917]
        expectOkStack "dispatch/loadintvar-not-handled-here"
          (runPlduqDispatchFallback plduxqInstr #[intV 5])
          #[intV 5, intV 917] }
  ]
  oracle := #[
    mkPlduqProxyCase "ok/w-1-a-1" 1 #[.slice (mkPatternSlice 1)],
    mkPlduqProxyCase "ok/w-1-a-5" 1 #[.slice (mkPatternSlice 5)],
    mkPlduqProxyCase "ok/w-2-a-2" 2 #[.slice (mkPatternSlice 2)],
    mkPlduqProxyCase "ok/w-7-a-11" 7 #[.slice (mkPatternSlice 11)],
    mkPlduqProxyCase "ok/w-8-a-8" 8 #[.slice (mkPatternSlice 8)],
    mkPlduqProxyCase "ok/w-16-a-20" 16 #[.slice (mkPatternSlice 20)],
    mkPlduqProxyCase "ok/w-31-a-63" 31 #[.slice (mkPatternSlice 63)],
    mkPlduqProxyCase "ok/w-64-a-64" 64 #[.slice (mkPatternSlice 64)],
    mkPlduqProxyCase "ok/w-127-a-140" 127 #[.slice (mkPatternSlice 140)],
    mkPlduqProxyCase "ok/w-128-a-256" 128 #[.slice (mkPatternSlice 256)],
    mkPlduqProxyCase "ok/w-255-a-255" 255 #[.slice (mkPatternSlice 255)],
    mkPlduqProxyCase "ok/w-256-a-256" 256 #[.slice (mkPatternSlice 256)],
    mkPlduqProxyCase "ok/deep-stack-null-below" 9 #[.null, .slice (mkPatternSlice 14)],
    mkPlduqProxyCase "ok/deep-stack-two-below" 5 #[intV (-7), .null, .slice (mkPatternSlice 9)],
    mkPlduqProxyCase "ok/refs/w-9-a-12-r-2" 9 #[.slice (mkPatternSliceWithRefs 12 #[refLeafA, refLeafB])],
    mkPlduqProxyCase "ok/refs/w-256-a-256-r-1" 256 #[.slice (mkPatternSliceWithRefs 256 #[refLeafA])],

    mkPlduqProxyCase "fail/w-1-a-0" 1 #[.slice (mkPatternSlice 0)],
    mkPlduqProxyCase "fail/w-2-a-1" 2 #[.slice (mkPatternSlice 1)],
    mkPlduqProxyCase "fail/w-8-a-7" 8 #[.slice (mkPatternSlice 7)],
    mkPlduqProxyCase "fail/w-16-a-0" 16 #[.slice (mkPatternSlice 0)],
    mkPlduqProxyCase "fail/w-64-a-63" 64 #[.slice (mkPatternSlice 63)],
    mkPlduqProxyCase "fail/w-128-a-127" 128 #[.slice (mkPatternSlice 127)],
    mkPlduqProxyCase "fail/w-256-a-255" 256 #[.slice (mkPatternSlice 255)],
    mkPlduqProxyCase "fail/deep-stack/w-64-a-10" 64 #[intV 33, .slice (mkPatternSlice 10)],
    mkPlduqProxyCase "fail/refs/w-5-a-4-r-1" 5 #[.slice (mkPatternSliceWithRefs 4 #[refLeafA])],
    mkPlduqProxyCase "fail/refs/w-256-a-128-r-2" 256 #[.slice (mkPatternSliceWithRefs 128 #[refLeafA, refLeafB])],

    mkPlduqProxyRawCase "underflow/empty" #[],
    mkPlduqProxyRawCase "underflow/one-item" #[intV 8],
    mkPlduqProxyRawCase "type/top-bits-not-int" #[.slice (mkPatternSlice 8), .null],
    mkPlduqProxyRawCase "type/top-slice-not-slice" #[.null, intV 8],
    mkPlduqProxyRawCase "range/bits-too-large" #[.slice (mkPatternSlice 16), intV 257],
    mkPlduqProxyRawCase "range/bits-negative" #[.slice (mkPatternSlice 16), intV (-1)],

    mkPlduqProxyRawCase "gas/exact-cost-succeeds"
      #[.slice (mkPatternSlice 14), intV 8]
      #[.pushInt (.num plduqProxySetGasExact), .tonEnvOp .setGasLimit, plduxqInstr],
    mkPlduqProxyRawCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkPatternSlice 14), intV 8]
      #[.pushInt (.num plduqProxySetGasExactMinusOne), .tonEnvOp .setGasLimit, plduxqInstr]
  ]
  fuzz := #[
    { seed := 2026021033
      count := 320
      gen := genPlduqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDUQ
