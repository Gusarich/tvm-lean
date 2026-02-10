import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDBEGINSX

/-
SDBEGINSX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/SdBeginsX.lean` (`.sdBeginsX quiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xd726`/`0xd727` decode + 13-bit `SDBEGINS{Q}` const family at `0xd728 >> 3`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sdBeginsX` encodes, `.sdBeginsConst` is not assemblable)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_begins_with`, `exec_slice_begins_with_common`)

Branch map covered by this suite:
- dispatch guard (`.sdBeginsX _` handled, everything else falls through to `next`);
- stack order and pop failures: first pop is prefix (`pref`), second pop is source (`s`);
- predicate branch: `s.haveBits prefLen && s.readBits prefLen == prefBits`;
- success branch: push remainder slice, and push `-1` only in quiet mode;
- failure branch: non-quiet throws `cellUnd`, quiet restores `s` and pushes `0`;
- opcode/decode boundaries around `0xd724`, `0xd726`, `0xd727`, invalid `0xd725`,
  and constant-prefix decode path (`0xd728 >> 3`) including truncation checks.
-/

private def sdbeginsxId : InstrId := { name := "SDBEGINSX" }

private def sdbeginsxInstr : Instr := .sdBeginsX false
private def sdbeginsxqInstr : Instr := .sdBeginsX true

private def sdsubstrInstr : Instr := .cellOp .sdSubstr

private def sdbeginsxWord : Nat := 0xd726
private def sdbeginsxqWord : Nat := 0xd727
private def sdbeginsConstPrefix13 : Nat := 0xd728 >>> 3

private def dispatchSentinel : Int := 726

private def mkSdbeginsxCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdbeginsxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdbeginsxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkSdbeginsxQuietCase
    (name : String)
    (stack : Array Value)
    (programPrefix : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkSdbeginsxCase name stack (programPrefix ++ #[sdbeginsxqInstr]) gasLimits fuel

private def runSdbeginsxDirect (quiet : Bool) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdBeginsX (.sdBeginsX quiet) stack

private def runSdbeginsxDirectNQ (stack : Array Value) :
    Except Excno (Array Value) :=
  runSdbeginsxDirect false stack

private def runSdbeginsxDirectQ (stack : Array Value) :
    Except Excno (Array Value) :=
  runSdbeginsxDirect true stack

private def runSdbeginsxDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdBeginsX instr (VM.push (intV dispatchSentinel)) stack

private def expectDecodeErr
    (label : String)
    (s : Slice)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError
        s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def expectDecodeBeginsConst
    (label : String)
    (s : Slice)
    (expectedQuiet : Bool)
    (expectedPrefixBits : BitString)
    (expectedBits : Nat := 21) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if bits != expectedBits then
        throw (IO.userError s!"{label}: expected consumed bits {expectedBits}, got {bits}")
      else
        match instr with
        | .sdBeginsConst quiet pref =>
            let prefBits := pref.readBits pref.bitsRemaining
            if quiet != expectedQuiet then
              throw (IO.userError
                s!"{label}: expected quiet={expectedQuiet}, got quiet={quiet}")
            else if prefBits != expectedPrefixBits then
              throw (IO.userError
                s!"{label}: expected prefix bits {expectedPrefixBits}, got {prefBits}")
            else
              pure s'
        | _ =>
            throw (IO.userError
              s!"{label}: expected .sdBeginsConst, got instr={reprStr instr}")

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

private def runSdbeginsxModel (quiet : Bool) (stack : Array Value) :
    Except Excno (Array Value) := do
  if stack.isEmpty then
    throw .stkUnd
  let prefV := stack.back!
  let st1 := stack.pop
  let pref ←
    match prefV with
    | .slice pref => pure pref
    | _ => throw .typeChk
  if st1.isEmpty then
    throw .stkUnd
  let sV := st1.back!
  let below := st1.pop
  let s ←
    match sV with
    | .slice s => pure s
    | _ => throw .typeChk
  let prefBits := pref.readBits pref.bitsRemaining
  let ok : Bool := s.haveBits prefBits.size && s.readBits prefBits.size == prefBits
  if ok then
    let out := below.push (.slice (s.advanceBits prefBits.size))
    if quiet then
      pure (out.push (intV (-1)))
    else
      pure out
  else if quiet then
    pure (below ++ #[.slice s, intV 0])
  else
    throw .cellUnd

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkWordSlice
    (bits : Nat)
    (word : Nat)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (natToBits word bits ++ tail) refs

private def mkStripeSlice
    (bits : Nat)
    (phase : Nat := 0)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase ++ tail) refs

private def mkSdBeginsConstRaw
    (quiet : Bool)
    (args7 : Nat)
    (rawData : BitString) : BitString :=
  natToBits sdbeginsConstPrefix13 13 ++
    natToBits ((if quiet then 0x80 else 0) + args7) 8 ++
    rawData

private def tailBits3 : BitString := natToBits 5 3
private def tailBits5 : BitString := natToBits 21 5
private def tailBits7 : BitString := natToBits 93 7

private def refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
private def refLeafB : Cell := Cell.mkOrdinary (natToBits 9 4) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 3 2) #[]

private def sliceEmpty : Slice := mkSliceWithBitsRefs #[]
private def prefEmpty : Slice := sliceEmpty
private def pref1 : Slice := mkWordSlice 1 1
private def pref5 : Slice := mkWordSlice 5 0x15
private def pref8A5 : Slice := mkWordSlice 8 0xa5
private def s8A5 : Slice := mkWordSlice 8 0xa5
private def s8FromPref5 : Slice := mkWordSlice 8 0xad
private def pref255 : Slice := mkStripeSlice 255 1
private def s256FromPref255 : Slice := mkStripeSlice 255 1 #[true]
private def pref256 : Slice := mkStripeSlice 256 0
private def s255 : Slice := mkStripeSlice 255 0

private def prefMismatchFirst8 : Slice := mkWordSlice 8 0x80
private def sMismatchFirst8 : Slice := mkWordSlice 8 0x00
private def prefMismatchMiddle8 : Slice := mkWordSlice 8 0xac
private def sMismatchMiddle8 : Slice := mkWordSlice 8 0xa4
private def prefMismatchLast8 : Slice := mkWordSlice 8 0xfe
private def sMismatchLast8 : Slice := mkWordSlice 8 0xff

private def pref8WithRefs : Slice := mkWordSlice 8 0xa5 #[] #[refLeafA, refLeafB]
private def s8WithOtherRefs : Slice := mkWordSlice 8 0xa5 #[] #[refLeafC]

private def cursorPrefCell : Cell :=
  Cell.mkOrdinary (tailBits3 ++ stripeBits 9 0) #[refLeafA, refLeafB]
private def cursorTargetCell : Cell :=
  Cell.mkOrdinary (tailBits5 ++ stripeBits 9 0 ++ tailBits7) #[refLeafC]
private def cursorTargetMismatchCell : Cell :=
  Cell.mkOrdinary (tailBits5 ++ stripeBits 9 1 ++ tailBits7) #[refLeafA, refLeafC]

private def cursorPref : Slice :=
  { cell := cursorPrefCell, bitPos := tailBits3.size, refPos := 1 }
private def cursorTarget : Slice :=
  { cell := cursorTargetCell, bitPos := tailBits5.size, refPos := 0 }
private def cursorTargetMismatch : Slice :=
  { cell := cursorTargetMismatchCell, bitPos := tailBits5.size, refPos := 1 }

private def constRawNonQuiet : BitString :=
  mkSdBeginsConstRaw false 0 #[true, true, false]
private def constRawQuiet : BitString :=
  mkSdBeginsConstRaw true 0 #[false, true, false]

private def sdbeginsxSetGasExact : Int :=
  computeExactGasBudget sdbeginsxInstr

private def sdbeginsxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdbeginsxInstr

private def expectedNQSuccess (below : Array Value) (s pref : Slice) : Array Value :=
  below ++ #[.slice (s.advanceBits pref.bitsRemaining)]

private def expectedQSuccess (below : Array Value) (s pref : Slice) : Array Value :=
  below ++ #[.slice (s.advanceBits pref.bitsRemaining), intV (-1)]

private def expectedQFail (below : Array Value) (s : Slice) : Array Value :=
  below ++ #[.slice s, intV 0]

def suite : InstrSuite where
  id := sdbeginsxId
  unit := #[
    -- Branch: non-quiet success path returns only the remainder slice and preserves below-stack values.
    { name := "unit/direct/nonquiet-success-core"
      run := do
        let checks : Array (String × Slice × Slice) :=
          #[
            ("ok/empty-empty", sliceEmpty, prefEmpty),
            ("ok/empty-prefix-vs-nonempty", s8A5, prefEmpty),
            ("ok/equal-8bits", s8A5, pref8A5),
            ("ok/proper-prefix-1-of-8", s8A5, pref1),
            ("ok/proper-prefix-5-of-8", s8FromPref5, pref5),
            ("ok/prefix-255-of-256", s256FromPref255, pref255),
            ("ok/refs-ignored", s8WithOtherRefs, pref8WithRefs),
            ("ok/cursor-prefix", cursorTarget, cursorPref)
          ]
        for (label, s, pref) in checks do
          expectOkStack label
            (runSdbeginsxDirectNQ #[.slice s, .slice pref])
            (expectedNQSuccess #[] s pref)

        let below : Array Value := #[.null, intV 17]
        expectOkStack "ok/deep-stack-preserved"
          (runSdbeginsxDirectNQ (below ++ #[.slice s8FromPref5, .slice pref5]))
          (expectedNQSuccess below s8FromPref5 pref5) }
    ,
    -- Branch: quiet mode splits success (`-1`) and failure (`0`) while preserving the source slice on failure.
    { name := "unit/direct/quiet-success-and-failure-contract"
      run := do
        let okChecks : Array (String × Slice × Slice) :=
          #[
            ("ok/equal-8bits", s8A5, pref8A5),
            ("ok/proper-prefix-5-of-8", s8FromPref5, pref5),
            ("ok/prefix-255-of-256", s256FromPref255, pref255),
            ("ok/cursor-prefix", cursorTarget, cursorPref)
          ]
        for (label, s, pref) in okChecks do
          expectOkStack s!"quiet/{label}"
            (runSdbeginsxDirectQ #[.slice s, .slice pref])
            (expectedQSuccess #[] s pref)

        let failChecks : Array (String × Slice × Slice) :=
          #[
            ("fail/mismatch-middle", sMismatchMiddle8, prefMismatchMiddle8),
            ("fail/nonempty-prefix-empty-target", sliceEmpty, pref5),
            ("fail/target-shorter-by-1", s255, pref256),
            ("fail/reversed-order", pref5, s8FromPref5),
            ("fail/cursor-mismatch", cursorTargetMismatch, cursorPref)
          ]
        for (label, s, pref) in failChecks do
          expectOkStack s!"quiet/{label}"
            (runSdbeginsxDirectQ #[.slice s, .slice pref])
            (expectedQFail #[] s)

        let below : Array Value := #[.null, intV (-9)]
        expectOkStack "quiet/ok/deep-stack-preserved"
          (runSdbeginsxDirectQ (below ++ #[.slice s8FromPref5, .slice pref5]))
          (expectedQSuccess below s8FromPref5 pref5)
        expectOkStack "quiet/fail/deep-stack-preserved"
          (runSdbeginsxDirectQ (below ++ #[.slice s255, .slice pref256]))
          (expectedQFail below s255) }
    ,
    -- Branch: non-quiet failure is `cellUnd`; stack argument order is `... s pref` (top is prefix).
    { name := "unit/direct/nonquiet-failure-and-stack-order"
      run := do
        expectErr "fail/nonempty-prefix-empty-target"
          (runSdbeginsxDirectNQ #[.slice sliceEmpty, .slice pref5]) .cellUnd
        expectErr "fail/mismatch-first-bit"
          (runSdbeginsxDirectNQ #[.slice sMismatchFirst8, .slice prefMismatchFirst8]) .cellUnd
        expectErr "fail/mismatch-middle-bit"
          (runSdbeginsxDirectNQ #[.slice sMismatchMiddle8, .slice prefMismatchMiddle8]) .cellUnd
        expectErr "fail/mismatch-last-bit"
          (runSdbeginsxDirectNQ #[.slice sMismatchLast8, .slice prefMismatchLast8]) .cellUnd
        expectErr "fail/target-shorter-than-prefix"
          (runSdbeginsxDirectNQ #[.slice s255, .slice pref256]) .cellUnd

        expectOkStack "order/s-then-pref-succeeds"
          (runSdbeginsxDirectNQ #[.slice s8FromPref5, .slice pref5])
          (expectedNQSuccess #[] s8FromPref5 pref5)
        expectErr "order/pref-then-s-fails"
          (runSdbeginsxDirectNQ #[.slice pref5, .slice s8FromPref5]) .cellUnd }
    ,
    -- Branch: pop ordering and type checks (`pref` pop first, then `s` pop).
    { name := "unit/direct/underflow-and-type-ordering"
      run := do
        expectErr "underflow/empty"
          (runSdbeginsxDirectNQ #[]) .stkUnd
        expectErr "underflow/one-slice"
          (runSdbeginsxDirectNQ #[.slice pref5]) .stkUnd

        expectErr "type/pref-top-null"
          (runSdbeginsxDirectNQ #[.slice s8FromPref5, .null]) .typeChk
        expectErr "type/pref-top-int"
          (runSdbeginsxDirectNQ #[.slice s8FromPref5, intV 3]) .typeChk
        expectErr "type/pref-top-cell"
          (runSdbeginsxDirectNQ #[.slice s8FromPref5, .cell refLeafA]) .typeChk

        expectErr "type/second-pop-after-valid-pref"
          (runSdbeginsxDirectNQ #[.null, .slice pref5]) .typeChk
        expectErr "type/second-pop-int-after-valid-pref"
          (runSdbeginsxDirectNQ #[intV 7, .slice pref5]) .typeChk

        expectErr "quiet/type/pref-top-null"
          (runSdbeginsxDirectQ #[.slice s8FromPref5, .null]) .typeChk
        expectErr "quiet/type/second-pop-after-valid-pref"
          (runSdbeginsxDirectQ #[.null, .slice pref5]) .typeChk }
    ,
    -- Branch invariant: SDBEGINSX has no integer immediates, so `rangeChk` is unreachable.
    { name := "unit/direct/rangechk-unreachable"
      run := do
        let probes : Array (String × Bool × Array Value) :=
          #[
            ("nonquiet-success", false, #[.slice s8FromPref5, .slice pref5]),
            ("nonquiet-fail", false, #[.slice s255, .slice pref256]),
            ("nonquiet-underflow", false, #[]),
            ("nonquiet-type", false, #[.slice s8FromPref5, .null]),
            ("quiet-success", true, #[.slice s8FromPref5, .slice pref5]),
            ("quiet-fail", true, #[.slice s255, .slice pref256]),
            ("quiet-underflow", true, #[.slice pref5]),
            ("quiet-type", true, #[.null, .slice pref5])
          ]
        for (label, quiet, stack) in probes do
          match runSdbeginsxDirect quiet stack with
          | .error .rangeChk =>
              throw (IO.userError s!"{label}: unexpected rangeChk for SDBEGINSX")
          | _ => pure () }
    ,
    -- Branch: direct implementation matches a tiny executable model on representative stacks.
    { name := "unit/model/alignment-on-representative-stacks"
      run := do
        let samples : Array (String × Array Value) :=
          #[
            ("ok/empty-empty", #[.slice sliceEmpty, .slice prefEmpty]),
            ("ok/proper-prefix", #[.slice s8FromPref5, .slice pref5]),
            ("ok/deep-stack", #[.null, intV 5, .slice s8FromPref5, .slice pref5]),
            ("err/nonquiet-mismatch", #[.slice sMismatchMiddle8, .slice prefMismatchMiddle8]),
            ("err/nonquiet-short-target", #[.slice s255, .slice pref256]),
            ("err/underflow", #[]),
            ("err/type-pref", #[.slice s8FromPref5, .null]),
            ("err/type-second-pop", #[.null, .slice pref5])
          ]
        for (label, stack) in samples do
          expectSameOutcome s!"model/nonquiet/{label}"
            (runSdbeginsxDirectNQ stack)
            (runSdbeginsxModel false stack)
          expectSameOutcome s!"model/quiet/{label}"
            (runSdbeginsxDirectQ stack)
            (runSdbeginsxModel true stack) }
    ,
    -- Branch: opcode/decode boundaries for `0xd726`/`0xd727` and neighboring/gap/const-prefix paths.
    { name := "unit/opcode/decode-assembler-and-const-boundaries"
      run := do
        let singleNQ ←
          match assembleCp0 [sdbeginsxInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/sdbeginsx failed: {e}")
        if singleNQ.bits = natToBits sdbeginsxWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdbeginsx: expected 0xd726, got bits {singleNQ.bits}")
        if singleNQ.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdbeginsx: expected 16 bits, got {singleNQ.bits.size}")

        let singleQ ←
          match assembleCp0 [sdbeginsxqInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/sdbeginsxq failed: {e}")
        if singleQ.bits = natToBits sdbeginsxqWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdbeginsxq: expected 0xd727, got bits {singleQ.bits}")

        let seqCode ←
          match assembleCp0 #[sdsubstrInstr, sdbeginsxInstr, sdbeginsxqInstr, .add].toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/seq failed: {e}")
        let s0 := Slice.ofCell seqCode
        let s1 ← expectDecodeStep "decode/seq-sdsubstr" s0 sdsubstrInstr 16
        let s2 ← expectDecodeStep "decode/seq-sdbeginsx" s1 sdbeginsxInstr 16
        let s3 ← expectDecodeStep "decode/seq-sdbeginsxq" s2 sdbeginsxqInstr 16
        let s4 ← expectDecodeStep "decode/seq-tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/seq-end: expected exhausted slice, got {s4.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawConstBits : BitString :=
          constRawNonQuiet ++
          natToBits sdbeginsxWord 16 ++
          constRawQuiet ++
          natToBits sdbeginsxqWord 16 ++
          addCell.bits
        let r0 := mkSliceFromBits rawConstBits
        let r1 ← expectDecodeBeginsConst "decode/raw-const-nq" r0 false #[true]
        let r2 ← expectDecodeStep "decode/raw-sdbeginsx" r1 sdbeginsxInstr 16
        let r3 ← expectDecodeBeginsConst "decode/raw-const-q" r2 true #[false]
        let r4 ← expectDecodeStep "decode/raw-sdbeginsxq" r3 sdbeginsxqInstr 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining")

        expectDecodeErr "decode/raw-gap-0xd725"
          (mkSliceFromBits (natToBits 0xd725 16))
          .invOpcode
        expectDecodeErr "decode/truncated-7b-sdbeginsx"
          (mkSliceFromBits (natToBits sdbeginsxWord 7))
          .invOpcode
        expectDecodeErr "decode/const-prefix-without-full-args"
          (mkSliceFromBits (natToBits sdbeginsConstPrefix13 13 ++ natToBits 0 7))
          .invOpcode
        expectDecodeErr "decode/const-missing-inline-bits"
          (mkSliceFromBits (natToBits sdbeginsConstPrefix13 13 ++ natToBits 1 8))
          .invOpcode

        match assembleCp0 [.sdBeginsConst false pref5] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/sdbegins-const: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/sdbegins-const: expected invOpcode, got success")

        match assembleCp0 [.sdBeginsConst true pref5] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/sdbeginsq-const: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/sdbeginsq-const: expected invOpcode, got success") }
    ,
    -- Branch: explicit `next` pass-through for non-target instructions.
    { name := "unit/dispatch/fallback-and-handled"
      run := do
        expectOkStack "dispatch/handled-nonquiet"
          (runSdbeginsxDispatchFallback sdbeginsxInstr #[.slice s8FromPref5, .slice pref5])
          (expectedNQSuccess #[] s8FromPref5 pref5)

        expectOkStack "dispatch/handled-quiet-fail"
          (runSdbeginsxDispatchFallback sdbeginsxqInstr #[.slice s255, .slice pref256])
          (expectedQFail #[] s255)

        expectOkStack "dispatch/non-target-add"
          (runSdbeginsxDispatchFallback .add #[.null, intV 9])
          #[.null, intV 9, intV dispatchSentinel]
        expectOkStack "dispatch/non-target-sdpfx"
          (runSdbeginsxDispatchFallback .sdPfx #[.slice s8FromPref5, .slice pref5])
          #[.slice s8FromPref5, .slice pref5, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdbeginsxCase "ok/nonquiet/empty-empty"
      #[.slice sliceEmpty, .slice prefEmpty],
    mkSdbeginsxCase "ok/nonquiet/empty-prefix-vs-nonempty"
      #[.slice s8A5, .slice prefEmpty],
    mkSdbeginsxCase "ok/nonquiet/equal-8bits"
      #[.slice s8A5, .slice pref8A5],
    mkSdbeginsxCase "ok/nonquiet/proper-prefix-1-of-8"
      #[.slice s8A5, .slice pref1],
    mkSdbeginsxCase "ok/nonquiet/proper-prefix-5-of-8"
      #[.slice s8FromPref5, .slice pref5],
    mkSdbeginsxCase "ok/nonquiet/prefix-255-of-256"
      #[.slice s256FromPref255, .slice pref255],
    mkSdbeginsxCase "ok/nonquiet/refs-ignored-prefix-side"
      #[.slice s8A5, .slice pref8WithRefs],
    mkSdbeginsxCase "ok/nonquiet/refs-ignored-target-side"
      #[.slice s8WithOtherRefs, .slice pref8A5],
    mkSdbeginsxCase "ok/nonquiet/deep-stack-preserve"
      #[.null, intV 21, .slice s8FromPref5, .slice pref5],

    mkSdbeginsxQuietCase "ok/quiet/equal-8bits"
      #[.slice s8A5, .slice pref8A5],
    mkSdbeginsxQuietCase "ok/quiet/proper-prefix-5-of-8"
      #[.slice s8FromPref5, .slice pref5],
    mkSdbeginsxQuietCase "ok/quiet/prefix-255-of-256"
      #[.slice s256FromPref255, .slice pref255],
    mkSdbeginsxQuietCase "ok/quiet/deep-stack-preserve"
      #[.null, intV (-4), .slice s8FromPref5, .slice pref5],

    mkSdbeginsxCase "fail/nonquiet/nonempty-prefix-empty-target"
      #[.slice sliceEmpty, .slice pref5],
    mkSdbeginsxCase "fail/nonquiet/mismatch-middle-bit"
      #[.slice sMismatchMiddle8, .slice prefMismatchMiddle8],
    mkSdbeginsxCase "fail/nonquiet/target-shorter-than-prefix"
      #[.slice s255, .slice pref256],
    mkSdbeginsxCase "fail/nonquiet/reversed-order"
      #[.slice pref5, .slice s8FromPref5],

    mkSdbeginsxQuietCase "fail/quiet/nonempty-prefix-empty-target"
      #[.slice sliceEmpty, .slice pref5],
    mkSdbeginsxQuietCase "fail/quiet/mismatch-last-bit"
      #[.slice sMismatchLast8, .slice prefMismatchLast8],
    mkSdbeginsxQuietCase "fail/quiet/target-shorter-than-prefix"
      #[.slice s255, .slice pref256],
    mkSdbeginsxQuietCase "fail/quiet/reversed-order-deep-preserve"
      #[.null, intV 99, .slice pref5, .slice s8FromPref5],

    mkSdbeginsxCase "underflow/empty"
      #[],
    mkSdbeginsxCase "underflow/one-slice"
      #[.slice pref5],
    mkSdbeginsxCase "type/top-pref-not-slice"
      #[.slice s8FromPref5, .null],
    mkSdbeginsxCase "type/second-pop-not-slice"
      #[.null, .slice pref5],

    mkSdbeginsxCase "gas/nonquiet/exact-cost-succeeds"
      #[.slice s8FromPref5, .slice pref5]
      #[.pushInt (.num sdbeginsxSetGasExact), .tonEnvOp .setGasLimit, sdbeginsxInstr],
    mkSdbeginsxCase "gas/nonquiet/exact-minus-one-out-of-gas"
      #[.slice s8FromPref5, .slice pref5]
      #[.pushInt (.num sdbeginsxSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdbeginsxInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDBEGINSX
