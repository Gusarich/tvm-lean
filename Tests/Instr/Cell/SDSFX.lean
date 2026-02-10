import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDSFX

/-
SDSFX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.sdSfx`, `sliceBitsSuffixEq`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc70c` decode to `.cellOp .sdSfx`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.cellOp .sdSfx` encode as `0xc70c`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`SDSFX` registration via `is_suffix_of`)
  - `/Users/daniil/Coding/ton/crypto/vm/cells/CellSlice.cpp` (`CellSlice::is_suffix_of`)

Branch map used for this suite:
- instruction dispatch (`SDSFX` handled; other instructions fall through to `next`);
- `checkUnderflow 2` before type checks;
- pop/type order (`top` then `second`) via `popSlice`;
- suffix predicate split (`true -> -1`, `false -> 0`) on remaining bits only (refs ignored).
-/

private def sdsfxId : InstrId := { name := "SDSFX" }

private def sdsfxInstr : Instr :=
  .cellOp .sdSfx

private def sdsfxRevInstr : Instr :=
  .cellOp .sdSfxRev

private def sdpsfxInstr : Instr :=
  .cellOp .sdPsfx

private def dispatchSentinel : Int := 50956

private def sdsfxOpcode : Nat := 0xc70c

private def execSdsfxOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp .sdSfx => execCellOpExt .sdSfx next
  | _ => next

private def execSdsfxRevOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp .sdSfxRev => execCellOpExt .sdSfxRev next
  | _ => next

private def mkSdsfxCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdsfxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdsfxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdsfxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execSdsfxOnly sdsfxInstr stack

private def runSdsfxRevDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execSdsfxRevOnly sdsfxRevInstr stack

private def runSdsfxDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execSdsfxOnly instr (VM.push (intV dispatchSentinel)) stack

private def expectSameOutcome
    (label : String)
    (lhs rhs : Except Excno (Array Value)) : IO Unit := do
  let same :=
    match lhs, rhs with
    | .ok ls, .ok rs => ls == rs
    | .error le, .error re => le == re
    | _, _ => false
  if same then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected identical outcomes, got lhs={reprStr lhs}, rhs={reprStr rhs}")

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def invertBits (bs : BitString) : BitString :=
  bs.map (fun b => !b)

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkSliceCursor
    (bits : BitString)
    (refs : Array Cell)
    (bitPos refPos : Nat) : Slice :=
  { cell := Cell.mkOrdinary bits refs, bitPos := bitPos, refPos := refPos }

private def boolFlag (b : Bool) : Value :=
  intV (if b then -1 else 0)

private def expectSdsfxResult
    (label : String)
    (s1 s2 : Slice)
    (expected : Bool)
    (stackPrefix : Array Value := #[]) : IO Unit :=
  expectOkStack label
    (runSdsfxDirect (stackPrefix ++ #[.slice s1, .slice s2]))
    (stackPrefix ++ #[boolFlag expected])

private def refA : Cell :=
  Cell.mkOrdinary (natToBits 5 3) #[]

private def refB : Cell :=
  Cell.mkOrdinary (natToBits 9 4) #[]

private def refC : Cell :=
  Cell.mkOrdinary (natToBits 3 2) #[]

private def cursorBits : BitString :=
  natToBits 0x2d5 10

private def cursorRefs : Array Cell :=
  #[refA, refB]

private def cursorWhole : Slice :=
  mkSliceCursor cursorBits cursorRefs 2 1

private def cursorSuffix : Slice :=
  mkSliceCursor cursorBits cursorRefs 5 0

private def cursorMismatch : Slice :=
  mkSliceWithBitsRefs (natToBits 0x16 5)

private def gasSuffix : Slice :=
  mkSliceWithBitsRefs (natToBits 0x5 3)

private def gasWhole : Slice :=
  mkSliceWithBitsRefs (natToBits 0x25 6) #[refA]

private def sdsfxSetGasExact : Int :=
  computeExactGasBudget sdsfxInstr

private def sdsfxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdsfxInstr

private def sdsfxLenPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickSdsfxLen (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (sdsfxLenPool.size - 1)
  (sdsfxLenPool[idx]!, rng')

private def pickRefPack (rng : StdGen) : Array Cell × StdGen :=
  let (pick, rng') := randNat rng 0 3
  let refs :=
    if pick = 0 then #[]
    else if pick = 1 then #[refA]
    else if pick = 2 then #[refA, refB]
    else #[refA, refB, refC]
  (refs, rng')

private def pickNoise (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 4
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 77
    else if pick = 2 then .cell refA
    else if pick = 3 then .slice (mkSliceWithBitsRefs (stripeBits 5 1) #[refB])
    else .builder Builder.empty
  (v, rng')

private def genSdsfxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    let (len, rng2) := pickSdsfxLen rng1
    let (phase, rng3) := randNat rng2 0 1
    let bits := stripeBits len phase
    (mkSdsfxCase s!"fuzz/ok/equal/len-{len}"
      #[.slice (mkSliceWithBitsRefs bits), .slice (mkSliceWithBitsRefs bits)], rng3)
  else if shape = 1 then
    let (sufLen, rng2) := pickSdsfxLen rng1
    let (prefLen, rng3) := randNat rng2 1 64
    let (phase, rng4) := randNat rng3 0 1
    let suffixBits := stripeBits sufLen phase
    let wholeBits := stripeBits prefLen (phase + 1) ++ suffixBits
    (mkSdsfxCase s!"fuzz/ok/proper/suf-{sufLen}/pref-{prefLen}"
      #[.slice (mkSliceWithBitsRefs suffixBits), .slice (mkSliceWithBitsRefs wholeBits)], rng4)
  else if shape = 2 then
    let (sufLen, rng2) := randNat rng1 1 128
    let (prefLen, rng3) := randNat rng2 0 64
    let (phase, rng4) := randNat rng3 0 1
    let suffixBits := stripeBits sufLen phase
    let wholeBits := stripeBits prefLen (phase + 1) ++ invertBits suffixBits
    (mkSdsfxCase s!"fuzz/false/mismatch/suf-{sufLen}/pref-{prefLen}"
      #[.slice (mkSliceWithBitsRefs suffixBits), .slice (mkSliceWithBitsRefs wholeBits)], rng4)
  else if shape = 3 then
    let (wholeLen, rng2) := pickSdsfxLen rng1
    let (delta, rng3) := randNat rng2 1 32
    let (phase, rng4) := randNat rng3 0 1
    let wholeBits := stripeBits wholeLen phase
    let suffixBits := stripeBits (wholeLen + delta) (phase + 1)
    (mkSdsfxCase s!"fuzz/false/longer/suf-{wholeLen + delta}/whole-{wholeLen}"
      #[.slice (mkSliceWithBitsRefs suffixBits), .slice (mkSliceWithBitsRefs wholeBits)], rng4)
  else if shape = 4 then
    let (wholeLen, rng2) := pickSdsfxLen rng1
    let (phase, rng3) := randNat rng2 0 1
    (mkSdsfxCase s!"fuzz/ok/empty-suffix/whole-{wholeLen}"
      #[.slice (mkSliceWithBitsRefs #[]), .slice (mkSliceWithBitsRefs (stripeBits wholeLen phase))], rng3)
  else if shape = 5 then
    let (len, rng2) := randNat rng1 1 128
    let (phase, rng3) := randNat rng2 0 1
    (mkSdsfxCase s!"fuzz/false/nonempty-vs-empty/suf-{len}"
      #[.slice (mkSliceWithBitsRefs (stripeBits len phase)), .slice (mkSliceWithBitsRefs #[])], rng3)
  else if shape = 6 then
    let (sufLen, rng2) := randNat rng1 0 64
    let (prefLen, rng3) := randNat rng2 0 64
    let (phase, rng4) := randNat rng3 0 1
    let suffixBits := stripeBits sufLen phase
    let wholeBits := stripeBits prefLen (phase + 1) ++ suffixBits
    let (sufRefs, rng5) := pickRefPack rng4
    let (wholeRefs, rng6) := pickRefPack rng5
    (mkSdsfxCase s!"fuzz/ok/refs-ignored/suf-{sufLen}/pref-{prefLen}"
      #[.slice (mkSliceWithBitsRefs suffixBits sufRefs), .slice (mkSliceWithBitsRefs wholeBits wholeRefs)], rng6)
  else if shape = 7 then
    let (sufLen, rng2) := randNat rng1 0 64
    let (prefLen, rng3) := randNat rng2 0 64
    let (phase, rng4) := randNat rng3 0 1
    let suffixBits := stripeBits sufLen phase
    let wholeBits := stripeBits prefLen (phase + 1) ++ suffixBits
    let (noise1, rng5) := pickNoise rng4
    let (noise2, rng6) := pickNoise rng5
    (mkSdsfxCase s!"fuzz/ok/deep/suf-{sufLen}/pref-{prefLen}"
      #[noise1, noise2, .slice (mkSliceWithBitsRefs suffixBits), .slice (mkSliceWithBitsRefs wholeBits)], rng6)
  else if shape = 8 then
    (mkSdsfxCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 9 then
    (mkSdsfxCase "fuzz/underflow/one-slice"
      #[.slice (mkSliceWithBitsRefs (stripeBits 8 0))], rng1)
  else if shape = 10 then
    (mkSdsfxCase "fuzz/underflow/one-null" #[.null], rng1)
  else if shape = 11 then
    (mkSdsfxCase "fuzz/type/top-null"
      #[.slice (mkSliceWithBitsRefs (stripeBits 3 0)), .null], rng1)
  else if shape = 12 then
    (mkSdsfxCase "fuzz/type/second-not-slice-int"
      #[intV 11, .slice (mkSliceWithBitsRefs (stripeBits 8 1))], rng1)
  else if shape = 13 then
    (mkSdsfxCase "fuzz/type/top-cell"
      #[.slice (mkSliceWithBitsRefs (stripeBits 3 1)), .cell refA], rng1)
  else if shape = 14 then
    (mkSdsfxCase "fuzz/gas/exact"
      #[.slice gasSuffix, .slice gasWhole]
      #[.pushInt (.num sdsfxSetGasExact), .tonEnvOp .setGasLimit, sdsfxInstr], rng1)
  else
    (mkSdsfxCase "fuzz/gas/exact-minus-one"
      #[.slice gasSuffix, .slice gasWhole]
      #[.pushInt (.num sdsfxSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdsfxInstr], rng1)

def suite : InstrSuite where
  id := { name := "SDSFX" }
  unit := #[
    { name := "unit/direct/suffix-boolean-outcomes"
      run := do
        let whole8 := mkSliceWithBitsRefs (natToBits 0xA5 8)
        let same8 := mkSliceWithBitsRefs (natToBits 0xA5 8)
        let suf3 := mkSliceWithBitsRefs (natToBits 0x5 3)
        let nonsuf3 := mkSliceWithBitsRefs (natToBits 0x6 3)
        let bit1 := mkSliceWithBitsRefs (natToBits 1 1)
        let diff8 := mkSliceWithBitsRefs (natToBits 0xA4 8)
        let empty := mkSliceWithBitsRefs #[]

        expectSdsfxResult "ok/equal-8bits" same8 whole8 true
        expectSdsfxResult "ok/proper-suffix-3-of-8" suf3 whole8 true
        expectSdsfxResult "ok/proper-suffix-1-of-8" bit1 whole8 true
        expectSdsfxResult "ok/empty-suffix" empty whole8 true
        expectSdsfxResult "ok/empty-suffix-empty-whole" empty empty true

        expectSdsfxResult "false/not-suffix-3-of-8" nonsuf3 whole8 false
        expectSdsfxResult "false/longer-than-whole" whole8 suf3 false
        expectSdsfxResult "false/nonempty-vs-empty" suf3 empty false
        expectSdsfxResult "false/equal-length-diff" diff8 whole8 false }
    ,
    { name := "unit/direct/cursor-and-ref-behavior"
      run := do
        expectSdsfxResult "ok/cursor-proper-suffix" cursorSuffix cursorWhole true
        expectSdsfxResult "false/cursor-mismatch" cursorMismatch cursorWhole false

        let refEqL := mkSliceWithBitsRefs (natToBits 0xD 4) #[refA, refB]
        let refEqR := mkSliceWithBitsRefs (natToBits 0xD 4) #[refC]
        expectSdsfxResult "ok/refs-ignored-equal-bits" refEqL refEqR true

        let refSuf := mkSliceWithBitsRefs (natToBits 0x5 3) #[refA]
        let refWhole := mkSliceWithBitsRefs (natToBits 0x25 6) #[refB, refC]
        expectSdsfxResult "ok/refs-ignored-proper-suffix" refSuf refWhole true

        expectSdsfxResult "ok/deep-stack-preserved" refSuf refWhole true #[.null, intV 17] }
    ,
    { name := "unit/direct/underflow-type-and-order"
      run := do
        let s := mkSliceWithBitsRefs (natToBits 0xA5 8)
        let t := mkSliceWithBitsRefs (natToBits 0x5 3)

        expectErr "underflow/empty"
          (runSdsfxDirect #[]) .stkUnd
        expectErr "underflow/one-slice"
          (runSdsfxDirect #[.slice s]) .stkUnd
        expectErr "underflow/one-null"
          (runSdsfxDirect #[.null]) .stkUnd

        expectErr "type/top-null"
          (runSdsfxDirect #[.slice t, .null]) .typeChk
        expectErr "type/top-int"
          (runSdsfxDirect #[.slice t, intV 4]) .typeChk
        expectErr "type/top-cell"
          (runSdsfxDirect #[.slice t, .cell refA]) .typeChk
        expectErr "type/top-builder-empty"
          (runSdsfxDirect #[.slice t, .builder Builder.empty]) .typeChk
        expectErr "type/second-not-slice-null"
          (runSdsfxDirect #[.null, .slice s]) .typeChk
        expectErr "type/second-not-slice-int"
          (runSdsfxDirect #[intV 9, .slice s]) .typeChk
        expectErr "type/both-wrong-top-fails-first"
          (runSdsfxDirect #[.null, intV 3]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let canonical ←
          match assembleCp0 [sdsfxInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sdsfx failed: {e}")
        if canonical.bits = natToBits sdsfxOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdsfx: expected opcode 0xc70c, got bits {canonical.bits}")
        if canonical.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdsfx: expected 16 bits, got {canonical.bits.size}")

        let program : Array Instr := #[.sdPfx, sdsfxInstr, sdsfxRevInstr, sdpsfxInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/program failed: {e}")

        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sdpfx-neighbor" s0 .sdPfx 16
        let s2 ← expectDecodeStep "decode/sdsfx" s1 sdsfxInstr 16
        let s3 ← expectDecodeStep "decode/sdsfxrev-neighbor" s2 sdsfxRevInstr 16
        let s4 ← expectDecodeStep "decode/sdpsfx-neighbor" s3 sdpsfxInstr 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/program-end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let rawBits : BitString :=
          natToBits 0xc70b 16
            ++ natToBits sdsfxOpcode 16
            ++ natToBits 0xc70d 16
            ++ natToBits 0xc70f 16
            ++ natToBits 0xa0 8
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-sdppfxrev-neighbor" r0 .sdPpfxRev 16
        let r2 ← expectDecodeStep "decode/raw-sdsfx" r1 sdsfxInstr 16
        let r3 ← expectDecodeStep "decode/raw-sdsfxrev-neighbor" r2 sdsfxRevInstr 16
        let r4 ← expectDecodeStep "decode/raw-sdpsfxrev-neighbor" r3 (.cellOp .sdPsfxRev) 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/alias/sdsfxrev-aligns-when-operands-are-swapped"
      run := do
        let pairs : Array (String × Slice × Slice) :=
          #[
            ("equal-8", mkSliceWithBitsRefs (natToBits 0xA5 8), mkSliceWithBitsRefs (natToBits 0xA5 8)),
            ("proper-3-of-8", mkSliceWithBitsRefs (natToBits 0x5 3), mkSliceWithBitsRefs (natToBits 0xA5 8)),
            ("false-3-of-8", mkSliceWithBitsRefs (natToBits 0x6 3), mkSliceWithBitsRefs (natToBits 0xA5 8)),
            ("empty-vs-8", mkSliceWithBitsRefs #[], mkSliceWithBitsRefs (natToBits 0xA5 8)),
            ("refs-ignored", mkSliceWithBitsRefs (natToBits 0xD 4) #[refA, refB], mkSliceWithBitsRefs (natToBits 0xD 4) #[refC]),
            ("cursor", cursorSuffix, cursorWhole)
          ]
        for (label, s1, s2) in pairs do
          expectSameOutcome s!"align/{label}"
            (runSdsfxDirect #[.slice s1, .slice s2])
            (runSdsfxRevDirect #[.slice s2, .slice s1])

        let s := mkSliceWithBitsRefs (natToBits 0xA5 8)
        expectSameOutcome "align/underflow-empty"
          (runSdsfxDirect #[])
          (runSdsfxRevDirect #[])
        expectSameOutcome "align/type-top-null-vs-second-null"
          (runSdsfxDirect #[.slice s, .null])
          (runSdsfxRevDirect #[.null, .slice s]) }
    ,
    { name := "unit/dispatch/non-sdsfx-falls-through"
      run := do
        let s1 := mkSliceWithBitsRefs (natToBits 0x5 3)
        let s2 := mkSliceWithBitsRefs (natToBits 0xA5 8)
        expectOkStack "dispatch/non-cellop"
          (runSdsfxDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-sdsfxrev"
          (runSdsfxDispatchFallback sdsfxRevInstr #[.slice s1, .slice s2])
          #[.slice s1, .slice s2, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-sdpsfx"
          (runSdsfxDispatchFallback sdpsfxInstr #[.slice s1, .slice s2])
          #[.slice s1, .slice s2, intV dispatchSentinel]
        expectOkStack "dispatch/handled-sdsfx-no-sentinel"
          (runSdsfxDispatchFallback sdsfxInstr #[.slice s1, .slice s2])
          #[intV (-1)] }
  ]
  oracle := #[
    mkSdsfxCase "ok/equal/8bits"
      #[.slice (mkSliceWithBitsRefs (natToBits 0xA5 8)), .slice (mkSliceWithBitsRefs (natToBits 0xA5 8))],
    mkSdsfxCase "ok/proper/3-of-8"
      #[.slice (mkSliceWithBitsRefs (natToBits 0x5 3)), .slice (mkSliceWithBitsRefs (natToBits 0xA5 8))],
    mkSdsfxCase "ok/proper/1-of-8"
      #[.slice (mkSliceWithBitsRefs (natToBits 0x1 1)), .slice (mkSliceWithBitsRefs (natToBits 0xA5 8))],
    mkSdsfxCase "ok/empty-suffix/empty-whole"
      #[.slice (mkSliceWithBitsRefs #[]), .slice (mkSliceWithBitsRefs #[])],
    mkSdsfxCase "ok/empty-suffix/nonempty-whole"
      #[.slice (mkSliceWithBitsRefs #[]), .slice (mkSliceWithBitsRefs (natToBits 0x39 6))],
    mkSdsfxCase "ok/equal/64bits-stripe"
      #[.slice (mkSliceWithBitsRefs (stripeBits 64 1)), .slice (mkSliceWithBitsRefs (stripeBits 64 1))],
    mkSdsfxCase "ok/proper/63-of-127"
      #[.slice (mkSliceWithBitsRefs (stripeBits 63 0)),
        .slice (mkSliceWithBitsRefs (stripeBits 64 1 ++ stripeBits 63 0))],
    mkSdsfxCase "ok/proper/1-of-256"
      #[.slice (mkSliceWithBitsRefs (natToBits 1 1)),
        .slice (mkSliceWithBitsRefs (stripeBits 255 0 ++ natToBits 1 1))],
    mkSdsfxCase "ok/refs-ignored/equal-bits-different-refs"
      #[.slice (mkSliceWithBitsRefs (natToBits 0xD 4) #[refA, refB]),
        .slice (mkSliceWithBitsRefs (natToBits 0xD 4) #[refC])],
    mkSdsfxCase "ok/refs-ignored/proper-suffix"
      #[.slice (mkSliceWithBitsRefs (natToBits 0x5 3) #[refA]),
        .slice (mkSliceWithBitsRefs (natToBits 0x25 6) #[refB, refC])],
    mkSdsfxCase "ok/deep-stack-preserve-null"
      #[.null, .slice (mkSliceWithBitsRefs (natToBits 0x5 3)), .slice (mkSliceWithBitsRefs (natToBits 0x25 6))],
    mkSdsfxCase "ok/deep-stack-preserve-int-and-cell"
      #[.cell refA, intV (-9), .slice (mkSliceWithBitsRefs (natToBits 0x5 3)),
        .slice (mkSliceWithBitsRefs (natToBits 0x25 6) #[refB])],

    mkSdsfxCase "false/not-suffix/3-of-8"
      #[.slice (mkSliceWithBitsRefs (natToBits 0x6 3)), .slice (mkSliceWithBitsRefs (natToBits 0xA5 8))],
    mkSdsfxCase "false/longer-than-whole"
      #[.slice (mkSliceWithBitsRefs (natToBits 0xA5 8)), .slice (mkSliceWithBitsRefs (natToBits 0x5 3))],
    mkSdsfxCase "false/nonempty-suffix-empty-whole"
      #[.slice (mkSliceWithBitsRefs (natToBits 0x5 3)), .slice (mkSliceWithBitsRefs #[])],
    mkSdsfxCase "false/equal-length-bit-diff"
      #[.slice (mkSliceWithBitsRefs (natToBits 0xA4 8)), .slice (mkSliceWithBitsRefs (natToBits 0xA5 8))],
    mkSdsfxCase "false/mismatch-tail-on-large"
      #[.slice (mkSliceWithBitsRefs (stripeBits 63 0)),
        .slice (mkSliceWithBitsRefs (stripeBits 64 1 ++ stripeBits 63 1))],
    mkSdsfxCase "false/refs-present-but-bits-mismatch"
      #[.slice (mkSliceWithBitsRefs (natToBits 0x5 3) #[refA, refB]),
        .slice (mkSliceWithBitsRefs (natToBits 0x26 6) #[refC])],
    mkSdsfxCase "false/deep-stack-preserve"
      #[.null, .slice (mkSliceWithBitsRefs (natToBits 0x6 3)), .slice (mkSliceWithBitsRefs (natToBits 0xA5 8))],

    mkSdsfxCase "underflow/empty" #[],
    mkSdsfxCase "underflow/one-slice" #[.slice (mkSliceWithBitsRefs (natToBits 0xA5 8))],
    mkSdsfxCase "underflow/one-null" #[.null],

    mkSdsfxCase "type/top-null"
      #[.slice (mkSliceWithBitsRefs (natToBits 0x5 3)), .null],
    mkSdsfxCase "type/top-int"
      #[.slice (mkSliceWithBitsRefs (natToBits 0x5 3)), intV 7],
    mkSdsfxCase "type/top-cell"
      #[.slice (mkSliceWithBitsRefs (natToBits 0x5 3)), .cell refA],
    mkSdsfxCase "type/top-builder-empty"
      #[.slice (mkSliceWithBitsRefs (natToBits 0x5 3)), .builder Builder.empty],
    mkSdsfxCase "type/second-not-slice-null"
      #[.null, .slice (mkSliceWithBitsRefs (natToBits 0xA5 8))],
    mkSdsfxCase "type/second-not-slice-int"
      #[intV 11, .slice (mkSliceWithBitsRefs (natToBits 0xA5 8))],
    mkSdsfxCase "type/both-wrong-top-first"
      #[.null, intV 3],

    mkSdsfxCase "gas/exact-cost-succeeds"
      #[.slice gasSuffix, .slice gasWhole]
      #[.pushInt (.num sdsfxSetGasExact), .tonEnvOp .setGasLimit, sdsfxInstr],
    mkSdsfxCase "gas/exact-minus-one-out-of-gas"
      #[.slice gasSuffix, .slice gasWhole]
      #[.pushInt (.num sdsfxSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdsfxInstr]
  ]
  fuzz := #[
    { seed := 2026021037
      count := 320
      gen := genSdsfxFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDSFX
