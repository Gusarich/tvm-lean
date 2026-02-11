import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.NEWC

/-
NEWC branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Newc.lean` (`execInstrCellNewc`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc8` decode to `.newc`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.newc` encodes as canonical `0xc8`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_new_builder`, opcode table entry `0xc8`).

Branch map used for this suite:
- Lean NEWC path: 1 branch site / 2 outcomes
  (`.newc` pushes empty builder; non-`.newc` falls through to `next`).
- C++ NEWC path: stack-growth-only terminal behavior
  (push fresh empty builder; no pops, no quiet/error sub-branches).

Key risk areas:
- stack-growth semantics (preserve all below-stack values, append exactly one empty builder);
- repeated NEWC composition (N invocations should push N builders);
- canonical single-byte opcode/decode boundary around `0xc8` with neighbors;
- gas cliff for `PUSHINT n; SETGASLIMIT; NEWC`.
-/

private def newcId : InstrId := { name := "NEWC" }

private def newcInstr : Instr := .newc

private def mkNewcCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[newcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := newcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkNewcProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := newcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runNewcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellNewc newcInstr stack

private def runNewcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellNewc .add (VM.push (intV 924)) stack

private def newcSetGasExact : Int :=
  computeExactGasBudget newcInstr

private def newcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne newcInstr

private def mkRepeatedNewcProgram (n : Nat) : Array Instr :=
  Array.replicate n newcInstr

private def mkStoreOnNewBuilderProgram
    (bits : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[newcInstr]
  else
    #[newcInstr, .pushInt x, .xchg0 1, .stu bits]

private def mkStoreOnNewBuilderThenEndcProgram
    (bits : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  mkStoreOnNewBuilderProgram bits x ++ #[.endc]

private def newcDoubleProgram : Array Instr :=
  mkRepeatedNewcProgram 2

private def newcTripleProgram : Array Instr :=
  mkRepeatedNewcProgram 3

private def newcQuadProgram : Array Instr :=
  mkRepeatedNewcProgram 4

private def newcStore1Program : Array Instr :=
  mkStoreOnNewBuilderProgram 1 (.num 1)

private def newcStore8Program : Array Instr :=
  mkStoreOnNewBuilderProgram 8 (.num 173)

private def newcStore16Program : Array Instr :=
  mkStoreOnNewBuilderProgram 16 (.num 65535)

private def newcStore256Program : Array Instr :=
  mkStoreOnNewBuilderProgram 256 (.num 0)

private def newcStore8EndcProgram : Array Instr :=
  mkStoreOnNewBuilderThenEndcProgram 8 (.num 173)

private def newcStore256EndcProgram : Array Instr :=
  mkStoreOnNewBuilderThenEndcProgram 256 (.num 0)

private def newcBuild1023Program : Array Instr :=
  build1023WithFixed .stu

private def newcBuild1023EndcProgram : Array Instr :=
  build1023WithFixed .stu ++ #[.endc]

private def newcEndcNewcStrefProgram : Array Instr :=
  #[.newc, .endc, .newc, .stref]

private def newcStoredCell8ThenStrefProgram : Array Instr :=
  mkStoreOnNewBuilderThenEndcProgram 8 (.num 173) ++ #[.newc, .stref]

private def newcStoredCell16ThenStrefProgram : Array Instr :=
  mkStoreOnNewBuilderThenEndcProgram 16 (.num 65535) ++ #[.newc, .stref]

private def newcDoubleThenStbProgram : Array Instr :=
  #[.newc, .newc, .stb false false]

private def newcTripleThenStbTwiceProgram : Array Instr :=
  #[.newc, .newc, .newc, .stb false false, .stb false false]

private def newcNoiseThenDoubleProgram : Array Instr :=
  #[.pushNull, .pushInt (.num 7)] ++ newcDoubleProgram

private def newcNoiseThenStore4Program : Array Instr :=
  #[.pushNull, .pushInt (.num 7)] ++ mkStoreOnNewBuilderProgram 4 (.num 9)

private def newcStoreBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickStoreBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (newcStoreBitsBoundaryPool.size - 1)
  (newcStoreBitsBoundaryPool[idx]!, rng')

private def pickPayloadForBits (bits : Nat) (rng0 : StdGen) : IntVal × StdGen :=
  if bits = 0 then
    (.num 0, rng0)
  else
    let hi : Int := intPow2 bits - 1
    let (pick, rng1) := randNat rng0 0 4
    let x : Int :=
      if pick = 0 then 0
      else if pick = 1 then 1
      else if pick = 2 then hi
      else if pick = 3 then
        if hi > 0 then hi - 1 else 0
      else
        hi / 2
    (.num x, rng1)

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 17
    else if pick = 2 then .cell Cell.empty
    else .builder Builder.empty
  (v, rng1)

private def genNewcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    (mkNewcCase "fuzz/ok/direct/empty" #[], rng1)
  else if shape = 1 then
    let (noise, rng2) := pickNoiseValue rng1
    (mkNewcCase "fuzz/ok/direct/noise-below" #[noise], rng2)
  else if shape = 2 then
    let (noise1, rng2) := pickNoiseValue rng1
    let (noise2, rng3) := pickNoiseValue rng2
    (mkNewcCase "fuzz/ok/direct/deep-stack" #[noise1, noise2], rng3)
  else if shape = 3 then
    (mkNewcProgramCase "fuzz/ok/program/double-newc" #[] newcDoubleProgram, rng1)
  else if shape = 4 then
    (mkNewcProgramCase "fuzz/ok/program/triple-newc" #[] newcTripleProgram, rng1)
  else if shape = 5 then
    (mkNewcProgramCase "fuzz/ok/program/quad-newc" #[] newcQuadProgram, rng1)
  else if shape = 6 then
    let (bits, rng2) := pickStoreBitsBoundary rng1
    let (x, rng3) := pickPayloadForBits bits rng2
    (mkNewcProgramCase s!"fuzz/ok/program/store-bits-{bits}" #[]
      (mkStoreOnNewBuilderProgram bits x), rng3)
  else if shape = 7 then
    let (bits, rng2) := pickStoreBitsBoundary rng1
    let (x, rng3) := pickPayloadForBits bits rng2
    (mkNewcProgramCase s!"fuzz/ok/program/store-bits-{bits}-then-endc" #[]
      (mkStoreOnNewBuilderThenEndcProgram bits x), rng3)
  else if shape = 8 then
    (mkNewcProgramCase "fuzz/ok/program/build-1023" #[] newcBuild1023Program, rng1)
  else if shape = 9 then
    (mkNewcProgramCase "fuzz/ok/program/newc-endc-newc-stref" #[] newcEndcNewcStrefProgram, rng1)
  else if shape = 10 then
    let (bits, rng2) := pickStoreBitsBoundary rng1
    let (x, rng3) := pickPayloadForBits bits rng2
    (mkNewcProgramCase s!"fuzz/ok/program/stored-cell-{bits}-then-stref" #[]
      (mkStoreOnNewBuilderThenEndcProgram bits x ++ #[.newc, .stref]), rng3)
  else if shape = 11 then
    (mkNewcProgramCase "fuzz/ok/program/newc-newc-stb" #[] newcDoubleThenStbProgram, rng1)
  else if shape = 12 then
    (mkNewcCase "fuzz/gas/exact" #[]
      #[.pushInt (.num newcSetGasExact), .tonEnvOp .setGasLimit, newcInstr], rng1)
  else
    (mkNewcCase "fuzz/gas/exact-minus-one" #[]
      #[.pushInt (.num newcSetGasExactMinusOne), .tonEnvOp .setGasLimit, newcInstr], rng1)

def suite : InstrSuite where
  id := newcId
  unit := #[
    { name := "unit/direct/push-empty-builder-and-preserve-below"
      run := do
        expectOkStack "ok/empty-stack"
          (runNewcDirect #[])
          #[.builder Builder.empty]

        expectOkStack "ok/preserve-null-below"
          (runNewcDirect #[.null])
          #[.null, .builder Builder.empty]

        expectOkStack "ok/preserve-int-and-cell-below"
          (runNewcDirect #[intV 9, .cell Cell.empty])
          #[intV 9, .cell Cell.empty, .builder Builder.empty]

        expectOkStack "ok/preserve-builder-below"
          (runNewcDirect #[.builder fullBuilder1023])
          #[.builder fullBuilder1023, .builder Builder.empty] }
    ,
    { name := "unit/direct/repeated-newc-stack-growth"
      run := do
        let s1 ←
          match runNewcDirect #[] with
          | .ok st => pure st
          | .error e => throw (IO.userError s!"repeat/first-empty: expected success, got {e}")
        expectOkStack "repeat/second-empty"
          (runNewcDirect s1)
          #[.builder Builder.empty, .builder Builder.empty]

        let s2 ←
          match runNewcDirect #[.null, intV 3] with
          | .ok st => pure st
          | .error e => throw (IO.userError s!"repeat/first-noise: expected success, got {e}")
        expectOkStack "repeat/second-noise"
          (runNewcDirect s2)
          #[.null, intV 3, .builder Builder.empty, .builder Builder.empty] }
    ,
    { name := "unit/opcode/decode-and-assembler-canonical"
      run := do
        let encoded ←
          match assembleCp0 [newcInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/newc failed: {e}")
        if encoded.bits = natToBits 0xc8 8 then
          pure ()
        else
          throw (IO.userError s!"assemble/newc: expected bits 0xc8, got {encoded.bits}")

        let program : Array Instr := #[newcInstr, .endc, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/newc" s0 newcInstr 8
        let s2 ← expectDecodeStep "decode/endc" s1 .endc 8
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/sequence-end: expected exhausted slice, got {s3.bitsRemaining} bits remaining")

        let raw := mkSliceFromBits (natToBits 0xc8 8 ++ natToBits 0xa0 8)
        let r1 ← expectDecodeStep "decode/raw-newc" raw newcInstr 8
        let r2 ← expectDecodeStep "decode/raw-tail-add" r1 .add 8
        if r2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/opcode/decode-boundaries-and-truncated-prefix"
      run := do
        let expectInvOpcode : String → Slice → IO Unit := fun label s =>
          match decodeCp0WithBits s with
          | .error .invOpcode => pure ()
          | .error e => throw (IO.userError s!"{label}: expected invOpcode, got {e}")
          | .ok (instr, bits, _) =>
              throw (IO.userError s!"{label}: expected invOpcode, decoded {instr} ({bits} bits)")

        let c9 := mkSliceFromBits (natToBits 0xc9 8)
        let c9' ← expectDecodeStep "decode/neighbor-c9-endc" c9 .endc 8
        if c9'.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/neighbor-c9-end: expected exhausted slice, got {c9'.bitsRemaining} bits remaining")

        let c8c7 := mkSliceFromBits (natToBits 0xc8 8 ++ natToBits 0xc7 8)
        let tail ← expectDecodeStep "decode/c8c7-first-newc" c8c7 newcInstr 8
        expectInvOpcode "decode/c8c7-truncated-second" tail

        expectInvOpcode "decode/truncated-c7-alone"
          (mkSliceFromBits (natToBits 0xc7 8)) }
    ,
    { name := "unit/dispatch/non-newc-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runNewcDispatchFallback #[.null])
          #[.null, intV 924] }
  ]
  oracle := #[
    mkNewcCase "ok/direct/empty-stack" #[],
    mkNewcCase "ok/direct/preserve-null-below" #[.null],
    mkNewcCase "ok/direct/preserve-int-below" #[intV 42],
    mkNewcCase "ok/direct/preserve-cell-below" #[.cell Cell.empty],
    mkNewcCase "ok/direct/preserve-empty-builder-below" #[.builder Builder.empty],
    mkNewcCase "ok/direct/preserve-mixed-below" #[.null, intV (-3), .cell Cell.empty],

    mkNewcProgramCase "ok/program/double-newc" #[] newcDoubleProgram,
    mkNewcProgramCase "ok/program/triple-newc" #[] newcTripleProgram,
    mkNewcProgramCase "ok/program/quad-newc" #[] newcQuadProgram,
    mkNewcProgramCase "ok/program/newc-endc" #[] #[.newc, .endc],
    mkNewcProgramCase "ok/program/newc-store-1bit" #[] newcStore1Program,
    mkNewcProgramCase "ok/program/newc-store-8bits" #[] newcStore8Program,
    mkNewcProgramCase "ok/program/newc-store-16bits" #[] newcStore16Program,
    mkNewcProgramCase "ok/program/newc-store-256bits" #[] newcStore256Program,
    mkNewcProgramCase "ok/program/newc-store-8bits-endc" #[] newcStore8EndcProgram,
    mkNewcProgramCase "ok/program/newc-store-256bits-endc" #[] newcStore256EndcProgram,
    mkNewcProgramCase "ok/program/newc-build-1023bits" #[] newcBuild1023Program,
    mkNewcProgramCase "ok/program/newc-build-1023bits-endc" #[] newcBuild1023EndcProgram,
    mkNewcProgramCase "ok/program/newc-endc-newc-stref" #[] newcEndcNewcStrefProgram,
    mkNewcProgramCase "ok/program/newc-stored-cell8-endc-newc-stref" #[] newcStoredCell8ThenStrefProgram,
    mkNewcProgramCase "ok/program/newc-stored-cell16-endc-newc-stref" #[] newcStoredCell16ThenStrefProgram,
    mkNewcProgramCase "ok/program/newc-newc-stb" #[] newcDoubleThenStbProgram,
    mkNewcProgramCase "ok/program/newc-newc-newc-stb-stb" #[] newcTripleThenStbTwiceProgram,
    mkNewcProgramCase "ok/program/noise-then-double-newc" #[] newcNoiseThenDoubleProgram,
    mkNewcProgramCase "ok/program/noise-then-newc-store4" #[] newcNoiseThenStore4Program,

    mkNewcCase "gas/exact-cost-succeeds" #[]
      #[.pushInt (.num newcSetGasExact), .tonEnvOp .setGasLimit, newcInstr],
    mkNewcCase "gas/exact-minus-one-out-of-gas" #[]
      #[.pushInt (.num newcSetGasExactMinusOne), .tonEnvOp .setGasLimit, newcInstr]
  ]
  fuzz := #[
    { seed := 2026021011
      count := 500
      gen := genNewcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.NEWC
