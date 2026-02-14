import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.PFXDICTGETEXEC

/-!
INSTRUCTION: PFXDICTGETEXEC

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch path.
   - `.dictExt (.pfxGet .getExec)` is handled only by `execInstrDictExt`.
   - any other instruction must continue to `next`.

2. [B2] Stack and arity ordering.
   - `checkUnderflow 3` consumes operands in order: `n`, `dict`, `cs`.
   - missing operands throw `.stkUnd` before type/range checks.

3. [B3] `n` validation (`popNatUpTo 1023`).
   - non-int for `n` -> `.typeChk`.
   - `.nan`, negative, and `> 1023` -> `.rangeChk`.

4. [B4] Dictionary operand validation.
   - `popMaybeCell` accepts `.null` and `.cell`.
   - `.builder`, `.tuple`, `.int`, `.slice`, etc. -> `.typeChk`.

5. [B5] Key operand validation.
   - key must be `.slice`; any other type -> `.typeChk`.

6. [B6] Lookup miss paths.
   - when key is not found (including `null` dict, prefix mismatch, shorter/longer key mismatch,
     or unmatched key shape), `.pfxGetExec` raises `.cellUnd`.

7. [B7] Lookup hit paths + prefix split.
   - on success, the matched prefix is split from `cs0` with
     `DictExt.slicePrefix`.
   - `pfxSlice` is pushed first, then remainder `cs1`.
   - this includes boundary `n = 0` and `n = 1023` cases.

8. [B8] Continuation transfer.
   - on hit, the value slice is converted into a continuation and executed via `callTo`.
   - `c0` is updated through `OrdCregs` callback wrapping.

9. [B9] Dictionary structural errors.
   - malformed internal prefix dictionaries propagate `.dictErr` from `pfxLookupPrefixWithCells`.

10. [B10] Assembler/decoder behavior.
   - `.dictExt (.pfxGet .getExec)` encodes to exactly `0xF4AB`.
   - `0xF4A8..0xF4AB` decode to the PFXDICTGET family.
   - neighbors `0xF4AA` (GETJMP) and `0xF4AC` (start of PFXDICTSWITCH range) are handled outside this
     instruction and must be rejected in the `PFXDICTGETEXEC` dispatch oracle via opcode mismatch.

11. [B11] Gas accounting.
   - No variable charges in this path (`consumeCreatedGas`/`registerLoaded` only; no creator gas here).
   - fixed exact-cost semantics are expected.

12. [B12] Gas edge branches.
   - exact-budget must succeed, exact-budget-minus-one must fail.

TOTAL BRANCHES: 12
- Any branch not directly covered by dedicated oracle cases is covered through fuzz.
-/

private def suiteId : InstrId :=
  { name := "PFXDICTGETEXEC" }

private def instr : Instr :=
  .dictExt (.pfxGet .getExec)

private def dispatchSentinel : Int := 31_415

private def rawOpcode16 : Nat → Cell :=
  fun v => Cell.mkOrdinary (natToBits v 16) #[]

private def rawF4A8 : Cell := rawOpcode16 0xF4A8
private def rawF4A9 : Cell := rawOpcode16 0xF4A9
private def rawF4AA : Cell := rawOpcode16 0xF4AA
private def rawF4AB : Cell := rawOpcode16 0xF4AB
private def rawF4AC : Cell := rawOpcode16 0xF4AC
private def rawF4A0 : Cell := rawOpcode16 0xF4A0
private def rawF4B0 : Cell := rawOpcode16 0xF4B0
private def rawF4 : Cell := rawOpcode16 0xF4

private def methodA : Slice := mkSliceFromBits (natToBits 0xA111 16)
private def methodB : Slice := mkSliceFromBits (natToBits 0xA222 16)
private def methodC : Slice := mkSliceFromBits (natToBits 0xA333 16)
private def methodN0 : Slice := mkSliceFromBits (natToBits 0xA444 16)

private def key4A : BitString := natToBits 0xB 4 -- 1011
private def key4B : BitString := natToBits 0x3 4 -- 0011
private def key4C : BitString := natToBits 0x7 4 -- 0111
private def key4D : BitString := natToBits 0xA 4 -- 1010
private def key2A : BitString := natToBits 0x2 2 -- 10
private def key8LongMatch : BitString := natToBits 0xBC 8 -- 10111100
private def key8LongMiss : BitString := natToBits 0x4E 8 -- 01001110

private def mkDictPfxRoot! (label : String) (n : Nat) (entries : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (bits, value) := entry
      if bits.size != n then
        panic! s!"{label}: key size mismatch (size={bits.size}, n={n})"
      match dictSetSliceWithCells root bits value .set with
      | .ok (some newRoot, _ok, _created, _loaded) => root := newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected insertion failure (no new root)"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: no entries for dictionary construction"

private def dict4Root : Cell :=
  mkDictPfxRoot! "dict4/root" 4 #[(key4A, methodA), (key4B, methodB)]

private def dict4RootSingle : Cell :=
  mkDictPfxRoot! "dict4/single" 4 #[(key4C, methodC)]

private def dict0Root : Cell :=
  mkDictPfxRoot! "dict0/root" 0 #[(#[], methodN0)]

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 1 1) #[]

private def mkStack (key : BitString) (dict : Value) (n : Int) : Array Value :=
  #[.slice (mkSliceFromBits key), dict, intV n]

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt .add (VM.push (intV dispatchSentinel)) stack

private def runRaw
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty)
    : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrDictExt instr (pure ())).run st0

private def expectRawOk
    (label : String)
    (res : Except Excno Unit × VmState) : IO VmState := do
  let (r, st) := res
  match r with
  | .ok _ => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErr
    (label : String)
    (res : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  let (r, st) := res
  match r with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected error {expected}, got success")
  | .error e =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")

private def expectDecodeInvOpcode (label : String) (w16 : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits w16 16)) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr instr}")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def expectMethodCont (label : String) (expected : Slice) (actual : Continuation) : IO Unit := do
  match actual with
  | .ordinary code (.quit 0) _ _ =>
      if code != expected then
        throw (IO.userError s!"{label}: expected continuation {reprStr expected}, got {reprStr code}")
  | _ =>
      throw (IO.userError s!"{label}: expected ordinary continuation, got {reprStr actual}")

private def callReturnFromCc (oldCc : Continuation) (oldC0 : Continuation) : Continuation :=
  match oldCc with
  | .ordinary code _ _ _ =>
      .ordinary code (.quit 0) ({ OrdCregs.empty with c0 := some oldC0 }) { stack := #[], nargs := -1 }
  | _ => .quit 0

private def expectCallTransfer
    (label : String)
    (target : Slice)
    (oldCc : Continuation)
    (oldC0 : Continuation)
    (st : VmState) : IO Unit := do
  expectMethodCont (s!"{label}/continuation") target st.cc
  let expectedC0 := callReturnFromCc oldCc oldC0
  if st.regs.c0 != expectedC0 then
    throw (IO.userError s!"{label}: expected c0={reprStr expectedC0}, got {reprStr st.regs.c0}")
  if !st.stack.isEmpty then
    throw (IO.userError s!"{label}: expected empty stack after call, got {reprStr st.stack}")

private def exactGas : Int :=
  computeExactGasBudget instr

private def exactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr

private def exactGasLimits : OracleGasLimits :=
  oracleGasLimitsExact exactGas

private def exactGasLimitsMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne exactGasMinusOne

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

private def mkCodeCase
    (name : String)
    (code : Cell)
    (stack : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genPFXDICTGETEXEC (rng0 : StdGen) : OracleCase × StdGen :=
  let (tier, rng1) := randNat rng0 0 9
  let (shape, rng2) :=
    if tier < 6 then
      randNat rng1 0 17
    else if tier < 9 then
      let (s, r) := randNat rng1 0 12
      (18 + s, r)
    else
      let (s, r) := randNat rng1 0 4
      (31 + s, r)
  let (tag, rng3) := randNat rng2 0 999_999
  let case0 : OracleCase :=
    match shape with
    | 0 => mkCase "fuzz/underflow/0" #[]
    | 1 => mkCase "fuzz/underflow/1" #[.slice (mkSliceFromBits key4A)]
    | 2 => mkCase "fuzz/underflow/2" #[.slice (mkSliceFromBits key4A), .cell dict4Root]
    | 3 => mkCase "fuzz/err/n/not-int" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), .builder Builder.empty])
    | 4 => mkCase "fuzz/err/n/nan" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), .int .nan])
    | 5 => mkCase "fuzz/err/n/negative" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), intV (-1)])
    | 6 => mkCase "fuzz/err/n/too-large" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), intV 1024])
    | 7 => mkCase "fuzz/err/dict/builder" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), intV 4] |>.set! 1 (.builder Builder.empty))
    | 8 => mkCase "fuzz/err/dict/tuple" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), intV 4] |>.set! 1 (.tuple #[]))
    | 9 => mkCase "fuzz/err/dict/int" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), intV 4] |>.set! 1 (intV 7))
    | 10 => mkCase "fuzz/err/key/null" (#[(.cell dict4Root), .null, intV 4])
    | 11 => mkCase "fuzz/err/key/cell" (#[(.cell dict4Root), .cell Cell.empty, intV 4])
    | 12 => mkCase "fuzz/err/key/builder" (#[(.cell dict4Root), .builder Builder.empty, intV 4])
    | 13 => mkCase "fuzz/err/key/nan" (#[(.cell dict4Root), .int .nan, intV 4])
    | 14 => mkCase "fuzz/miss/null" (mkStack key4A (.null) 4)
    | 15 => mkCase "fuzz/miss/in-range" (mkStack key4D (.cell dict4Root) 4)
    | 16 => mkCase "fuzz/miss/key-short" (mkStack key2A (.cell dict4Root) 4)
    | 17 => mkCase "fuzz/miss/key-long" (mkStack key8LongMiss (.cell dict4Root) 4)
    | 18 => mkCase "fuzz/hit/exact-a" (mkStack key4A (.cell dict4Root) 4)
    | 19 => mkCase "fuzz/hit/exact-b" (mkStack key4B (.cell dict4Root) 4)
    | 20 => mkCase "fuzz/hit/long-key" (mkStack key8LongMatch (.cell dict4Root) 4)
    | 21 => mkCase "fuzz/hit/key-prefix-only" (mkStack key2A (.cell dict4RootSingle) 4)
    | 22 => mkCase "fuzz/hit/zero-n" #[.slice (mkSliceFromBits key8LongMatch), .cell dict0Root, intV 0]
    | 23 => mkCase "fuzz/hit/n-max" (mkStack key4A (.cell dict4Root) 1023)
    | 24 => mkCase "fuzz/hit/n-zero-key" (mkStack #[] (.cell dict4Root) 4)
    | 25 => mkCase "fuzz/malformed-root" (mkStack key4A (.cell malformedDictRoot) 4)
    | 26 =>
      mkCase
        "fuzz/gas/exact"
        (mkStack key4A (.cell dict4Root) 4)
        exactGasLimits
        1_000_000
        (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
    | 27 =>
      mkCase
        "fuzz/gas/exact-minus-one"
        (mkStack key4A (.cell dict4Root) 4)
        exactGasLimitsMinusOne
        1_000_000
        (#[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
    | 28 => mkCodeCase "fuzz/raw/f4ab" rawF4AB
    | 29 => mkCodeCase "fuzz/raw/f4aa" rawF4AA
    | 30 => mkCodeCase "fuzz/raw/f4ac" rawF4AC
    | 31 => mkCodeCase "fuzz/raw/f4a8" rawF4A8
    | 32 => mkCodeCase "fuzz/raw/truncated" rawF4
    | 33 => mkCodeCase "fuzz/raw/invalid" rawF4A0
    | 34 => mkCodeCase "fuzz/raw/outside" rawF4B0
    | 35 => mkCodeCase "fuzz/raw/f4a9" rawF4A9
    | _ => mkCodeCase "fuzz/raw/invalid-default" rawF4
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)


def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st := mkStack key4A (.cell dict4Root) 4
        expectOkStack "unit/dispatch/fallback" (runDispatchFallback st) #[intV dispatchSentinel] },
    { name := "unit/dispatch/match" -- [B1]
      run := do
        let _st := mkStack key4A (.cell dict4Root) 4
        expectOkStack "unit/dispatch/match" (runDispatchFallback (mkStack key4A (.cell dict4Root) 4)) #[] },
    { name := "unit/asm" -- [B10][B11]
      run := do
        match encodeCp0 instr with
        | .ok c =>
            if c != natToBits 0xF4AB 16 then
              throw (IO.userError s!"unit/asm: expected 0xF4AB, got {c}")
        | .error e => throw (IO.userError s!"unit/asm: expected success, got {e}")
        let _ ← expectDecodeStep "unit/decode/f4ab" (mkSliceFromBits (natToBits 0xF4AB 16)) instr 16
        expectDecodeInvOpcode "unit/decode/f4aa" 0xF4AA
        expectDecodeInvOpcode "unit/decode/f4ac" 0xF4AC
        expectDecodeInvOpcode "unit/decode/truncated" 0xF4 },
    { name := "unit/raw/call" -- [B8]
      run := do
        let st ←
          expectRawOk
            "unit/raw/call" 
            (runRaw (mkStack key4A (.cell dict4Root) 4) { Regs.initial with c0 := .quit 17 } (.ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty))
        expectCallTransfer "unit/raw/call" methodA (.ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty) (.quit 17) st },
    { name := "unit/raw/malformed" -- [B9]
      run := do
        let _ ←
          expectRawErr
            "unit/raw/malformed"
            (runRaw (mkStack key4A (.cell malformedDictRoot) 4) Regs.initial (.ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty))
            .dictErr
        pure () }
  ]
  oracle := #[
    mkCase "oracle/underflow/0" #[] -- [B2]
    , mkCase "oracle/underflow/1" #[.slice (mkSliceFromBits key4A)] -- [B2]
    , mkCase "oracle/underflow/2" #[.slice (mkSliceFromBits key4A), .cell dict4Root] -- [B2]
    , mkCase "oracle/err/n/not-int" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), .builder Builder.empty]) -- [B3]
    , mkCase "oracle/err/n/nan" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), .int .nan]) -- [B3]
    , mkCase "oracle/err/n/negative" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), intV (-1)]) -- [B3]
    , mkCase "oracle/err/n/too-large" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), intV 1024]) -- [B3]
    , mkCase "oracle/err/dict/builder" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), intV 4] |>.set! 1 (.builder Builder.empty)) -- [B4]
    , mkCase "oracle/err/dict/tuple" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), intV 4] |>.set! 1 (.tuple #[])) -- [B4]
    , mkCase "oracle/err/dict/int" (#[(.cell dict4Root), .slice (mkSliceFromBits key4A), intV 4] |>.set! 1 (intV 77)) -- [B4]
    , mkCase "oracle/err/key/null" (#[(.cell dict4Root), .null, intV 4]) -- [B5]
    , mkCase "oracle/err/key/cell" (#[(.cell dict4Root), .cell Cell.empty, intV 4]) -- [B5]
    , mkCase "oracle/err/key/builder" (#[(.cell dict4Root), .builder Builder.empty, intV 4]) -- [B5]
    , mkCase "oracle/err/key/nan" (#[(.cell dict4Root), .int .nan, intV 4]) -- [B5]
    , mkCase "oracle/miss/null" #[.slice (mkSliceFromBits key4A), .null, intV 4] -- [B6]
    , mkCase "oracle/miss/in-range" (mkStack key4D (.cell dict4Root) 4) -- [B6]
    , mkCase "oracle/miss/key-short" (mkStack key2A (.cell dict4Root) 4) -- [B6]
    , mkCase "oracle/miss/key-long" (mkStack key8LongMiss (.cell dict4Root) 4) -- [B6]
    , mkCase "oracle/miss/key-empty" (mkStack #[] (.cell dict4Root) 4) -- [B6]
    , mkCase "oracle/miss/key-prefix-only" (mkStack key2A (.cell dict4RootSingle) 4) -- [B6]
    , mkCase "oracle/hit/exact-a" (mkStack key4A (.cell dict4Root) 4) {} -- [B7]
    , mkCase "oracle/hit/exact-b" (mkStack key4B (.cell dict4Root) 4) -- [B7]
    , mkCase "oracle/hit/long-key" (mkStack key8LongMatch (.cell dict4Root) 4) -- [B7]
    , mkCase "oracle/hit/zero-n" (#[.slice (mkSliceFromBits key8LongMatch), .cell dict0Root, intV 0]) -- [B7]
    , mkCase "oracle/hit/n-max" (mkStack key4A (.cell dict4Root) 1023) -- [B7]
    , mkCase "oracle/malformed/root" (mkStack key4A (.cell malformedDictRoot) 4) -- [B9]
    , mkCodeCase "oracle/raw/f4a8" rawF4A8 -- [B10]
    , mkCodeCase "oracle/raw/f4a9" rawF4A9 -- [B10]
    , mkCodeCase "oracle/raw/f4aa" rawF4AA -- [B10]
    , mkCodeCase "oracle/raw/f4ab" rawF4AB -- [B10][B11]
    , mkCodeCase "oracle/raw/f4ac" rawF4AC -- [B10]
    , mkCodeCase "oracle/raw/truncated" rawF4 -- [B10]
    , mkCase -- [B12]
      "oracle/gas/exact"
      (mkStack key4A (.cell dict4Root) 4)
      exactGasLimits
      1_000_000
      (#[.pushInt (.num exactGas), .tonEnvOp .setGasLimit, instr])
    , mkCase -- [B12]
      "oracle/gas/exact-minus-one"
      (mkStack key4A (.cell dict4Root) 4)
      exactGasLimitsMinusOne
      1_000_000
      (#[.pushInt (.num exactGasMinusOne), .tonEnvOp .setGasLimit, instr])
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genPFXDICTGETEXEC }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.PFXDICTGETEXEC
