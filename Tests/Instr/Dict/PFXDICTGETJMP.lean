import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.PFXDICTGETJMP

/-!
INSTRUCTION: PFXDICTGETJMP

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch branch: `execInstrDictExt` handles `.dictExt (.pfxGet .getJmp)` and must continue via `next` for other instructions.
2. [B2] Runtime arity preconditions: `checkUnderflow 3` on `[key, dict, n]` before any typed/semantic checks.
3. [B3] `n` validation: `popNatUpTo 1023` must enforce type and range (`.typeChk`/`.rangeChk`) and reject negative or oversized values.
4. [B4] `dict` argument validation: `popMaybeCell` accepts `.cell` and `.null`; anything else is a type error.
5. [B5] `key` argument validation: `popSlice` accepts only `.slice`; wrong stack shape throws typed error.
6. [B6] Miss behavior for `.getJmp`: malformed traversal/matching miss returns original key slice and no extra boolean.
7. [B7] Hit behavior for `.getJmp`: pushes matched prefix and remaining key slice; control transfer is always jump using matched value slice as continuation.
8. [B8] Structural dictionary errors: malformed prefix nodes throw `.dictErr`.
9. [B9] Assembler/decoder mapping for opcode family:
   - `.dictExt (.pfxGet .getJmp)` ↔ `0xf4aa`.
   - Neighboring `0xf4a8`, `0xf4a9`, and `0xf4ab` are sibling opcodes.
   - Outside neighbors (`0xf4a7`, `0xf4ac`, `0xf4b0`) must decode as `.invOpcode`.
10. [B10] Gas behavior:
   - no variable branch cost in this op’s model; base cost is constant.
   - verify `exact` and `exact-1` gas boundary cases.

TOTAL BRANCHES: 10

Each oracle test below is tagged [Bn].
Any branch not covered by oracle tests is expected to be hit by the fuzz generator.
-/

private def suiteId : InstrId := { name := "PFXDICTGETJMP" }

private def instr : Instr := .dictExt (.pfxGet .getJmp)

private def dispatchSentinel : Int := 77_001

private def jumpTargetSlice : Slice := mkSliceFromBits (natToBits 0xC0DE 16)
private def altJumpTargetSlice : Slice := mkSliceFromBits (natToBits 0xBEEF 16)
private def shortKeyBits : Slice := mkSliceFromBits (natToBits 3 4)
private def shortMissBits : Slice := mkSliceFromBits (natToBits 10 4)
private def longHitBits : Slice := mkSliceFromBits (natToBits 0x3F 8)
private def longHitBitsMore : Slice := mkSliceFromBits (natToBits 0x3F3F 12)
private def longMissBits : Slice := mkSliceFromBits (natToBits 0xAF 8)
private def emptyKeyBits : Slice := mkSliceFromBits (natToBits 0 0)

private def mkDictFromPairs (label : String) (n : Nat) (pairs : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for pair in pairs do
      let keyBits : BitString :=
        match dictKeyBits? pair.1 n false with
        | some bits => bits
        | none => panic! s!"{label}: unsupported key ({pair.1}, n={n})"
      match dictSetSliceWithCells root keyBits pair.2 .set with
      | .ok (some next, _ok, _created, _loaded) => root := some next
      | .ok (none, _, _, _) => panic! s!"{label}: insertion returned none"
      | .error e => panic! s!"{label}: dict set failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary"

private def dictJmpHit : Value :=
  .cell (mkDictFromPairs "PFXDICTGETJMP::hit" 4 #[(3, jumpTargetSlice), (2, altJumpTargetSlice)])
private def dictJmpMissOnly : Value :=
  .cell (mkDictFromPairs "PFXDICTGETJMP::miss" 4 #[(2, altJumpTargetSlice)])
private def dictJmpN0 : Value :=
  .cell (mkDictFromPairs "PFXDICTGETJMP::n0" 0 #[(0, jumpTargetSlice)])
private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0 2) #[]

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def sentinelC0 : Continuation := .quit 99
private def regsWithSentinelC0 : Regs := { Regs.initial with c0 := sentinelC0 }

private def rawOpcode16 (w16 : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w16 16) #[]

private def runPfxDictGetJmpDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instr (VM.push (intV dispatchSentinel)) stack

private def runPfxDictGetJmpDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runPfxDictGetJmpRaw
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrDictExt instr (pure ())).run st0

private def expectRawOk (label : String) (res : Except Excno Unit × VmState) : IO VmState := do
  let (r, st) := res
  match r with
  | .ok _ => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErr (label : String) (res : Except Excno Unit × VmState) (expected : Excno) : IO VmState := do
  let (r, st) := res
  match r with
  | .ok _ => throw (IO.userError s!"{label}: expected error {expected}, got success")
  | .error e =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")

private def expectJumpTransfer (label : String) (target : Slice) (expectedC0 : Continuation) (st : VmState) : IO Unit := do
  match st.cc with
  | .ordinary code (.quit 0) _ _ =>
      if code != target then
        throw (IO.userError s!"{label}: expected continuation code {reprStr target}, got {reprStr code}")
  | _ => throw (IO.userError s!"{label}: expected ordinary continuation")
  if st.regs.c0 != expectedC0 then
    throw (IO.userError s!"{label}: expected c0 {reprStr expectedC0}, got {reprStr st.regs.c0}")
  if !st.stack.isEmpty then
    throw (IO.userError s!"{label}: expected empty stack, got {reprStr st.stack}")

private def expectMissPushKey (label : String) (expectedKey : Slice) (st : VmState) : IO Unit := do
  match st.stack.toList with
  | [ .slice got ] =>
      if got == expectedKey then
        pure ()
      else
        throw (IO.userError s!"{label}: expected key {reprStr expectedKey}, got {reprStr got}")
  | _ =>
      throw (IO.userError s!"{label}: expected single-slice stack, got {reprStr st.stack}")

private def expectDecodeInv (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode for {opcode}, decode returned {reprStr instr}")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode for {opcode}, got {e}")

private def expectDecodeStepExact (label : String) (instr : Instr) (w16 : Nat) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e => throw (IO.userError s!"{label}: assemble failed with {e}")
  | .ok c =>
      if c.bits != natToBits w16 16 then
        throw (IO.userError s!"{label}: expected bits {reprStr (natToBits w16 16)}, got {reprStr c.bits}")
      else
        let _ ← expectDecodeStep label (Slice.ofCell c) instr 16

private def gasExact : Int := computeExactGasBudget instr
private def gasExactMinusOne : Int := computeExactGasBudgetMinusOne instr
private def gasExactLimits : OracleGasLimits := oracleGasLimitsExact gasExact
private def gasExactMinusOneLimits : OracleGasLimits := oracleGasLimitsExactMinusOne gasExactMinusOne

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000)
    (program : Array Instr := #[instr]) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value := #[])
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def addSuffixToCaseName (name : String) (rng0 : StdGen) : String × StdGen :=
  let (sfx, rng1) := randNat rng0 0 999_999
  (s!"{name}/{sfx}", rng1)

private def genPFXDICTGETJMP (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let case0 : OracleCase :=
    if shape = 0 then
      mkCase "fuzz/underflow/0" #[]
    else if shape = 1 then
      mkCase "fuzz/underflow/1" #[(.slice shortKeyBits), dictJmpHit]
    else if shape = 2 then
      mkCase "fuzz/underflow/2" #[(.slice shortKeyBits), dictJmpHit]
    else if shape = 3 then
      mkCase "fuzz/err/n-type" #[(.slice shortKeyBits), dictJmpHit, (.tuple #[])]
    else if shape = 4 then
      mkCase "fuzz/err/n-nan" #[(.slice shortKeyBits), dictJmpHit, .int .nan]
    else if shape = 5 then
      mkCase "fuzz/err/n-negative" #[(.slice shortKeyBits), dictJmpHit, intV (-1)]
    else if shape = 6 then
      mkCase "fuzz/err/n-too-large" #[(.slice shortKeyBits), dictJmpHit, intV 1024]
    else if shape = 7 then
      mkCase "fuzz/err/dict-builder" #[(.slice shortKeyBits), .builder Builder.empty, intV 4]
    else if shape = 8 then
      mkCase "fuzz/err/dict-tuple" #[(.slice shortKeyBits), .tuple #[], intV 4]
    else if shape = 9 then
      mkCase "fuzz/err/key-int" #[(.int (.num 3)), dictJmpHit, intV 4]
    else if shape = 10 then
      mkCase "fuzz/err/key-null" #[(.null), dictJmpHit, intV 4]
    else if shape = 11 then
      mkCase "fuzz/err/key-cell" #[(.cell Cell.empty), dictJmpHit, intV 4]
    else if shape = 12 then
      mkCase "fuzz/err/key-nan" #[(.int .nan), dictJmpHit, intV 4]
    else if shape = 13 then
      mkCase "fuzz/miss/no-root" #[(.slice longMissBits), .null, intV 4]
    else if shape = 14 then
      mkCase "fuzz/miss/short-mismatch" #[(.slice shortMissBits), dictJmpHit, intV 4]
    else if shape = 15 then
      mkCase "fuzz/miss/long-mismatch" #[(.slice longMissBits), dictJmpHit, intV 4]
    else if shape = 16 then
      mkCase "fuzz/hit/short" #[(.slice shortKeyBits), dictJmpHit, intV 4]
    else if shape = 17 then
      mkCase "fuzz/hit/long" #[(.slice longHitBits), dictJmpHit, intV 4]
    else if shape = 18 then
      mkCase "fuzz/hit/longer" #[(.slice longHitBitsMore), dictJmpHit, intV 4]
    else if shape = 19 then
      mkCase "fuzz/hit/n0" #[(.slice shortKeyBits), dictJmpMissOnly, intV 0]
    else if shape = 20 then
      mkCase "fuzz/malformed-root" #[(.slice shortKeyBits), .cell malformedDict, intV 4]
    else if shape = 21 then
      mkCase
        "fuzz/gas/exact"
        #[(.slice shortKeyBits), dictJmpHit, intV 4]
        (program := #[.pushInt (.num gasExact), .tonEnvOp .setGasLimit, instr])
        (gasLimits := gasExactLimits)
    else if shape = 22 then
      mkCase
        "fuzz/gas/exact-minus-one"
        #[(.slice shortKeyBits), dictJmpHit, intV 4]
        (program := #[.pushInt (.num gasExactMinusOne), .tonEnvOp .setGasLimit, instr])
        (gasLimits := gasExactMinusOneLimits)
    else if shape = 23 then
      mkCase "fuzz/fallback/underflow-3" #[(.slice shortKeyBits)]
    else
      mkCase "fuzz/miss/null-root-long" #[(.slice longMissBits), .null, intV 4]
  let (name, rng2) := addSuffixToCaseName case0.name rng1
  ({ case0 with name := name }, rng2)


def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st := runPfxDictGetJmpDispatchFallback #[(.slice shortKeyBits), dictJmpHit, intV 4]
        expectOkStack "unit/dispatch/fallback" st #[intV dispatchSentinel] },
    { name := "unit/dispatch/match" -- [B1]
      run := do
        let st := runPfxDictGetJmpDispatchFallback #[(.slice shortKeyBits), dictJmpHit, intV 4]
        expectOkStack "unit/dispatch/match" st #[] },
    { name := "unit/encode-decode/f4aa" -- [B9]
      run := do
        expectDecodeStepExact "unit/asm/f4aa" instr 0xF4AA
        match decodeCp0WithBits (mkSliceFromBits (natToBits 0xF4AA 16)) with
        | .ok (actual, _, _) =>
            if actual != instr then
              throw (IO.userError s!"unit/asm/f4aa: expected {reprStr instr}, got {reprStr actual}")
        | .error e => throw (IO.userError s!"unit/asm/f4aa: decode failed {e}") },
    { name := "unit/decode/family-siblings" -- [B9]
      run := do
        match decodeCp0WithBits (mkSliceFromBits (natToBits 0xF4A8 16)) with
        | .ok (actual, _, _) =>
            match actual with
            | .dictExt (.pfxGet .getQ) => pure ()
            | _ => throw (IO.userError s!"unit/decode/f4a8: expected getQ, got {reprStr actual}")
        | .error e => throw (IO.userError s!"unit/decode/f4a8: expected success, got {e}")
        match decodeCp0WithBits (mkSliceFromBits (natToBits 0xF4AB 16)) with
        | .ok (actual, _, _) =>
            match actual with
            | .dictExt (.pfxGet .getExec) => pure ()
            | _ => throw (IO.userError s!"unit/decode/f4ab: expected getExec, got {reprStr actual}")
        | .error e => throw (IO.userError s!"unit/decode/f4ab: expected success, got {e}") },
    { name := "unit/decode/invalid-neighbors" -- [B9]
      run := do
        expectDecodeInv "unit/decode/f4a7" 0xF4A7
        expectDecodeInv "unit/decode/f4ac" 0xF4AC
        expectDecodeInv "unit/decode/f4b0" 0xF4B0 },
    { name := "unit/raw/jump-transfer" -- [B7, B8]
      run := do
        let st ←
          expectRawOk
            "unit/raw/jump-transfer"
            (runPfxDictGetJmpRaw #[(.slice longHitBits), dictJmpHit, intV 4] regsWithSentinelC0 defaultCc)
        expectJumpTransfer "unit/raw/jump-transfer" jumpTargetSlice sentinelC0 st },
    { name := "unit/raw/miss-null-root" -- [B6]
      run := do
        let st ←
          expectRawOk
            "unit/raw/miss-null-root"
            (runPfxDictGetJmpRaw #[(.slice longMissBits), .null, intV 4] regsWithSentinelC0 defaultCc)
        expectMissPushKey "unit/raw/miss-null-root" longMissBits st },
    { name := "unit/raw/malformed-root" -- [B8]
      run := do
        let _ ←
          expectRawErr
            "unit/raw/malformed-root"
            (runPfxDictGetJmpRaw #[(.slice shortKeyBits), .cell malformedDict, intV 4] regsWithSentinelC0 defaultCc)
            .dictErr
        pure () }
  ]
  oracle := #[
    -- [B2] Underflow.
    mkCase "oracle/underflow/0" #[],
    mkCase "oracle/underflow/1" #[(.slice shortKeyBits)],
    mkCase "oracle/underflow/2" #[(.slice shortKeyBits), dictJmpHit],

    -- [B3] Invalid `n` values.
    mkCase "oracle/err/n-type" #[(.slice shortKeyBits), dictJmpHit, .tuple #[]],
    mkCase "oracle/err/n-nan" #[(.slice shortKeyBits), dictJmpHit, .int .nan],
    mkCase "oracle/err/n-negative" #[(.slice shortKeyBits), dictJmpHit, intV (-1)],
    mkCase "oracle/err/n-too-large" #[(.slice shortKeyBits), dictJmpHit, intV 1024],

    -- [B4] Invalid dictionary values.
    mkCase "oracle/err/dict-builder" #[(.slice shortKeyBits), .builder Builder.empty, intV 4],
    mkCase "oracle/err/dict-tuple" #[(.slice shortKeyBits), .tuple #[], intV 4],
    mkCase "oracle/err/dict-cell-emptyslice" #[(.slice shortKeyBits), .cell Cell.empty, intV 4],

    -- [B5] Invalid key values.
    mkCase "oracle/err/key-int" #[(.int (.num 3)), dictJmpHit, intV 4],
    mkCase "oracle/err/key-null" #[(.null), dictJmpHit, intV 4],
    mkCase "oracle/err/key-builder" #[(.builder Builder.empty), dictJmpHit, intV 4],
    mkCase "oracle/err/key-tuple" #[(.tuple #[]), dictJmpHit, intV 4],
    mkCase "oracle/err/key-nan" #[(.int .nan), dictJmpHit, intV 4],

    -- [B6] Miss path.
    mkCase "oracle/miss/no-root-short" #[(.slice shortMissBits), .null, intV 4],
    mkCase "oracle/miss/no-root-long" #[(.slice longMissBits), .null, intV 4],
    mkCase "oracle/miss/mismatch-short" #[(.slice shortMissBits), dictJmpHit, intV 4],
    mkCase "oracle/miss/mismatch-long" #[(.slice longMissBits), dictJmpHit, intV 4],
    mkCase "oracle/miss/misfit-n" #[(.slice shortMissBits), dictJmpMissOnly, intV 4],

    -- [B7] Hit path and jump transfer input shapes.
    mkCase "oracle/hit/short" #[(.slice shortKeyBits), dictJmpHit, intV 4],
    mkCase "oracle/hit/long" #[(.slice longHitBits), dictJmpHit, intV 4],
    mkCase "oracle/hit/longer" #[(.slice longHitBitsMore), dictJmpHit, intV 4],
    mkCase "oracle/hit/n0" #[(.slice emptyKeyBits), dictJmpN0, intV 0],
    mkCase "oracle/hit/zero-nonempty-key" #[(.slice shortKeyBits), dictJmpMissOnly, intV 8],

    -- [B8] Malformed dictionary.
    mkCase "oracle/malformed-root" #[(.slice shortKeyBits), .cell malformedDict, intV 4],

    -- [B9] Decoder/encoder family edges.
    mkCaseCode "oracle/raw/f4aa" #[] (rawOpcode16 0xF4AA),
    mkCaseCode "oracle/raw/f4a8" #[] (rawOpcode16 0xF4A8),
    mkCaseCode "oracle/raw/f4a9" #[] (rawOpcode16 0xF4A9),
    mkCaseCode "oracle/raw/f4ab" #[] (rawOpcode16 0xF4AB),
    mkCaseCode "oracle/raw/f4a7" #[] (rawOpcode16 0xF4A7),
    mkCaseCode "oracle/raw/f4b0" #[] (rawOpcode16 0xF4B0),
    mkCaseCode "oracle/raw/f4ac" #[] (rawOpcode16 0xF4AC),

    -- [B10] Gas.
    mkCase "oracle/gas/exact" #[(.slice shortKeyBits), dictJmpHit, intV 4] gasExactLimits
      (program := #[.pushInt (.num gasExact), .tonEnvOp .setGasLimit, instr]),
    mkCase "oracle/gas/exact-minus-one" #[(.slice shortKeyBits), dictJmpHit, intV 4] gasExactMinusOneLimits
      (program := #[.pushInt (.num gasExactMinusOne), .tonEnvOp .setGasLimit, instr])
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genPFXDICTGETJMP }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.PFXDICTGETJMP
