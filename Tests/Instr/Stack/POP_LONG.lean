import Std
import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.POP_LONG

/-
INSTRUCTION: POP_LONG

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime success branch:
   - `VM.swap 0 idx` succeeds iff `idx < stack.size`.
   - On success, top element swaps with index `idx` from top, then `VM.pop` removes the top.
   - There is no type check (`pop` accepts any `Value`), so success depends only on stack depth.
2. [B2] Runtime underflow branch:
   - If `stack.size ≤ idx`, `VM.swap` fails via `check_underflow_p`, producing `.stkUnd` before mutation.
   - This is the only runtime failure mode for POP/POP_LONG execution.
3. [B3] Dispatch branch:
   - `execInstrStackPop` matches `.pop idx`, so instruction reaches this handler directly.
   - Non-POP variants must be rejected by dispatch and handled elsewhere.
4. [B4] Assembler short-range branch (`idx ∈ [0,15]`):
   - `0` → opcode `0x30`
   - `1` → opcode `0x31`
   - `2..15` → opcode `0x30 + idx` (`0x32..0x3f`)
5. [B5] Assembler long-range branch (`idx ∈ [16,255]`):
   - Encoded as `0x57` + one-byte index (`16` bits total).
   - `idx > 255` raises `.rangeChk`.
6. [B6] Decoder short branch:
   - `0x30`, `0x31`, and `0x32..0x3f` decode to `.pop 0`, `.pop 1`, `.pop idx` respectively.
7. [B7] Decoder long branch:
   - `0x57` then one-byte arg decodes to `.pop idx` for all `0..255`.
8. [B8] Decoder aliasing and neighbor boundaries:
   - `0x57 0x00` and `0x30`/`0x31` represent different encoding shapes for equivalent `.pop` semantics (no conflict in dispatch).
   - Adjacent non-pop opcodes must not be misclassified.
9. [B9] Decoder truncation branches:
   - Prefix `0x57` without argument (8 bits) fails with `.invOpcode`.
   - Prefix `0x57` + 7 bits (15 bits) also fails with `.invOpcode`.
10. [B10] Gas accounting:
   - `instrGas = gasPerInstr + totBits`, with `totBits=8` for short and `16` for long.
   - No variable penalty for index magnitude exists.
11. [B11] Gas boundary coverage:
   - exact budget should succeed.
   - exact-1 budget should fail (out-of-gas) for both short and long forms.

TOTAL BRANCHES: 11
-/

private def popLongId : InstrId := { name := "POP_LONG" }

private def popInstr (idx : Nat) : Instr := .pop idx

private def mkCase
    (name : String)
    (idx : Nat)
    (stack : Array Value)
    (program : Array Instr := #[popInstr idx])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := popLongId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := popLongId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasCase
    (name : String)
    (stack : Array Value)
    (idx : Nat)
    (setGasBudget : Int)
    (gasLimits : OracleGasLimits) : OracleCase :=
  { name := name
    instr := popLongId
    program := #[.pushInt (.num setGasBudget), .tonEnvOp .setGasLimit, popInstr idx]
    initStack := stack
    gasLimits := gasLimits }

private def runPopDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPop (popInstr idx) stack

private def runPopFallback (_idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPop .add (VM.push (intV 101)) stack

private def popShortExactGas : Int :=
  computeExactGasBudget (popInstr 1)

private def popShortGasMinusOne : Int :=
  computeExactGasBudgetMinusOne (popInstr 1)

private def popLongExactGas : Int :=
  computeExactGasBudget (popInstr 16)

private def popLongGasMinusOne : Int :=
  computeExactGasBudgetMinusOne (popInstr 16)

private def makeStack (n : Nat) : Array Value := Id.run do
  let mut out : Array Value := #[]
  for i in [0:n] do
    out := out.push (intV (Int.ofNat i + 1))
  return out

private def makeNoisyStack (n : Nat) : Array Value := Id.run do
  let mut out : Array Value := #[]
  for i in [0:n] do
    let v :=
      if i % 4 = 0 then
        .null
      else if i % 4 = 1 then
        .cell Cell.empty
      else if i % 4 = 2 then
        .builder Builder.empty
      else
        intV (Int.ofNat i)
    out := out.push v
  return out

private def popRaw8 (w8 : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w8 8) #[]

private def popRaw16 (idx : Nat) : Cell :=
  Cell.mkOrdinary ((natToBits 0x57 8) ++ (natToBits idx 8)) #[]

private def popRawShort0 : Cell := popRaw8 0x30
private def popRawShort1 : Cell := popRaw8 0x31
private def popRawShort15 : Cell := popRaw8 0x3f
private def popRawLong0 : Cell := popRaw16 0
private def popRawLong16 : Cell := popRaw16 16
private def popRawLong255 : Cell := popRaw16 255
private def popRawPop1Long : Cell := popRaw16 1
private def popRawTruncated8 : Cell := popRaw8 0x57
private def popRawTruncated15 : Cell := Cell.mkOrdinary (natToBits (0x57 >>> 1) 15) #[]
private def popRawNeighborOver : Cell := Cell.mkOrdinary ((natToBits 0x31 8) ++ (natToBits 0x21 8)) #[]

private def expectAssembleRangeErr (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e = .rangeChk then
        pure ()
      else
        throw (IO.userError s!"{label}: expected .rangeChk, got {e}")
  | .ok cell =>
      throw (IO.userError s!"{label}: expected assembly failure, got {reprStr cell}")

private def expectEncodeShortByte (label : String) (idx : Nat) (expectedByte : Nat) : IO Unit := do
  let code ←
    match assembleCp0 [popInstr idx] with
    | .error e => throw (IO.userError s!"{label}: assemble failed: {e}")
    | .ok c => pure c
  let (first, _) ←
    match (Slice.ofCell code).takeBitsAsNat 8 with
    | .error e => throw (IO.userError s!"{label}: cannot read encoded byte: {e}")
    | .ok x => pure x
  if first ≠ expectedByte then
    throw (IO.userError s!"{label}: expected first byte {expectedByte}, got {first}")
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e => throw (IO.userError s!"{label}: encoded .pop {idx} decode failed: {e}")
  | .ok (i', bits, tail) =>
      if reprStr i' != reprStr (popInstr idx) then
        throw (IO.userError s!"{label}: expected decode {reprStr (popInstr idx)}, got {reprStr i'}")
      else if bits ≠ 8 then
        throw (IO.userError s!"{label}: expected totBits=8, got {bits}")
      else if tail.bitsRemaining ≠ 0 then
        throw (IO.userError s!"{label}: expected no decode tail, got {tail.bitsRemaining} bits")
      else
        pure ()

private def expectEncodeLongWord (label : String) (idx : Nat) : IO Unit := do
  let code ←
    match assembleCp0 [popInstr idx] with
    | .error e => throw (IO.userError s!"{label}: assemble failed: {e}")
    | .ok c => pure c
  let bits ←
    match (Slice.ofCell code).takeBitsAsNat 16 with
    | .error e => throw (IO.userError s!"{label}: cannot read encoded 16 bits: {e}")
    | .ok (v, _) => pure v
  let expected := (0x57 <<< 8) + idx
  if bits ≠ expected then
    throw (IO.userError s!"{label}: expected encoded long form for idx {idx}, got {bits}")
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e => throw (IO.userError s!"{label}: encoded .pop {idx} decode failed: {e}")
  | .ok (i', bits', tail) =>
      if reprStr i' != reprStr (popInstr idx) then
        throw (IO.userError s!"{label}: expected decode {reprStr (popInstr idx)}, got {reprStr i'}")
      else if bits' ≠ 16 then
        throw (IO.userError s!"{label}: expected totBits=16, got {bits'}")
      else if tail.bitsRemaining ≠ 0 then
        throw (IO.userError s!"{label}: expected no decode tail, got {tail.bitsRemaining} bits")
      else
        pure ()

private def expectDecodeStep
    (label : String)
    (code : Cell)
    (expected : Instr)
    (expectedBits : Nat)
    (expectedTailBits : Nat := 0) : IO Slice := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")
  | .ok (i, bits, tail) =>
      if reprStr i != reprStr expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr i}")
      else if bits ≠ expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else if expectedTailBits ≠ 0 && tail.bitsRemaining ≠ expectedTailBits then
        throw (IO.userError s!"{label}: expected tail {expectedTailBits}, got {tail.bitsRemaining}")
      else
        pure tail

private def expectDecodeErr (label : String) (code : Cell) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (i, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error, got {reprStr i} ({bits} bits)")

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def popShortIdxPool : Array Nat := #[0, 1, 2, 3, 7, 15]
private def popLongIdxPool : Array Nat := #[16, 17, 31, 63, 127, 255]
private def popMixedIdxPool : Array Nat := #[0, 1, 4, 7, 15, 16, 17, 31, 63, 127, 255]

private def genPopLongFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (case0, rng2) :=
    if shape = 0 then
      let (idx, rng2) := pickFromPool popShortIdxPool rng1
      (mkCase s!"fuzz/ok/short-boundary-{idx}" idx (makeStack (idx + 1)), rng2)
    else if shape = 1 then
      let (idx, rng2) := pickFromPool popLongIdxPool rng1
      (mkCase s!"/fuzz/ok/long-boundary-{idx}" idx (makeNoisyStack (idx + 1)), rng2)
    else if shape = 2 then
      let (idx, rng2) := pickFromPool popMixedIdxPool rng1
      let st := (makeStack (idx + 2)).set! 0 (Value.cell Cell.empty)
      (mkCase s!"/fuzz/ok/type-mix-min-idx{idx}" idx st, rng2)
    else if shape = 3 then
      let (idx, rng2) := pickFromPool popLongIdxPool rng1
      (mkCase s!"/fuzz/ok/long-noise-idx{idx}" idx (makeNoisyStack (idx + 2)), rng2)
    else if shape = 4 then
      let (idx, rng2) := pickFromPool popShortIdxPool rng1
      let size : Nat := if idx = 0 then 0 else idx
      (mkCase s!"/fuzz/err/short-underflow-{idx}" idx (makeStack size), rng2)
    else if shape = 5 then
      let (idx, rng2) := pickFromPool popLongIdxPool rng1
      let size : Nat := if idx = 0 then 0 else idx
      (mkCase s!"/fuzz/err/long-underflow-{idx}" idx (makeNoisyStack size), rng2)
    else if shape = 6 then
      (mkCaseCode s!"/fuzz/ok/decode/short-raw-31" #[intV 11, intV 12] popRawShort1, rng1)
    else if shape = 7 then
      (mkCaseCode s!"/fuzz/ok/decode/long-raw-16" (makeStack 17) popRawLong16, rng1)
    else if shape = 8 then
      (mkGasCase s!"/fuzz/gas/exact-short-1/{shape}" (makeStack 2) 1 popShortExactGas (oracleGasLimitsExact popShortExactGas), rng1)
    else if shape = 9 then
      (mkGasCase s!"/fuzz/gas/exact-minus-one-short-1/{shape}" (makeStack 2) 1 popShortGasMinusOne (oracleGasLimitsExact popShortGasMinusOne), rng1)
    else if shape = 10 then
      (mkGasCase s!"/fuzz/gas/exact-long-16/{shape}" (makeStack 18) 16 popLongExactGas (oracleGasLimitsExact popLongExactGas), rng1)
    else
      (mkGasCase s!"/fuzz/gas/exact-minus-one-long-16/{shape}" (makeStack 18) 16 popLongGasMinusOne (oracleGasLimitsExact popLongGasMinusOne), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def oracleCases : Array OracleCase := #[
  -- [B4]/[B6] short path/short decode pair.
  mkCase "ok/short/idx0-singleton" 0 #[intV 11],
  -- [B4]/[B6] short path at minimal depth for idx1.
  mkCase "ok/short/idx1-two-items" 1 #[intV 10, intV 20],
  -- [B1] short path with non-int values preserved.
  mkCase "ok/short/idx0-with-mix" 0 #[.null, intV 7, .tuple #[]],
  -- [B4] short path near boundary, idx2.
  mkCase "ok/short/idx2" 2 #[intV 101, intV 202, intV 303],
  -- [B4] short path boundary idx3.
  mkCase "ok/short/idx3" 3 (makeNoisyStack 4),
  -- [B4] short boundary idx7.
  mkCase "ok/short/idx7/noise" 7 (makeNoisyStack 8),
  -- [B4] short max boundary idx15.
  mkCase "ok/short/idx15/max" 15 (makeNoisyStack 16),
  -- [B5]/[B8] long path lower bound idx16.
  mkCase "ok/long/idx16/min-depth" 16 (makeStack 17),
  -- [B5]/[B8] long middle idx31.
  mkCase "ok/long/idx31" 31 (makeNoisyStack 32),
  -- [B5]/[B8] long idx63.
  mkCase "ok/long/idx63" 63 (makeNoisyStack 64),
  -- [B5]/[B8] long idx127.
  mkCase "ok/long/idx127" 127 (makeNoisyStack 128),
  -- [B5]/[B8] long max idx255.
  mkCase "ok/long/idx255-max" 255 (makeNoisyStack 256),
  -- [B5]/[B8] long with mixed stack size above max boundary.
  mkCase "ok/long/idx255-extra-depth" 255 (makeNoisyStack 260),

  -- [B2] underflow empty stack.
  mkCase "err/underflow/empty-idx0" 0 #[],
  -- [B2] underflow empty stack for nonzero idx.
  mkCase "err/underflow/empty-idx1" 1 #[],
  -- [B2] underflow singleton for idx1.
  mkCase "err/underflow/one-item-idx1" 1 #[intV 9],
  -- [B2] underflow insufficient depth for short idx2.
  mkCase "err/underflow/two-items-idx3" 3 #[intV 1, intV 2],
  -- [B2] underflow one below required idx15.
  mkCase "err/underflow/size15-idx15" 15 #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10, intV 11, intV 12, intV 13, intV 14, intV 15],
  -- [B2] underflow long idx16 boundary.
  mkCase "err/underflow/size16-idx16" 16 (makeStack 16),
  -- [B2] underflow deep long idx127.
  mkCase "err/underflow/size127-idx127" 127 (makeStack 127),
  -- [B2] underflow deep max idx255.
  mkCase "err/underflow/size255-idx255" 255 (makeStack 255),
  -- [B3] success with nontrivial alias at x=y edge style.
  mkCase "ok/program/alias-tail" 7 #[intV 7, intV 8, intV 9, intV 10, intV 11, intV 12, intV 13],
  -- [B1] success then follow-up no-op-style probe.
  mkCase "ok/program/followup-pop-then-drop" 1
    #[intV 10, intV 20] #[.pop 1, .pop 0],

  -- [B6] decode raw short form via opcode 0x30.
  mkCaseCode "ok/decode/raw-30-short" #[intV 10, intV 20] popRawShort0,
  -- [B6] decode raw short form via opcode 0x31.
  mkCaseCode "ok/decode/raw-31-short" #[intV 11, intV 12, intV 13] popRawShort1,
  -- [B6] decode raw short max form via opcode 0x3f.
  mkCaseCode "ok/decode/raw-3f-short" (makeStack 16) popRawShort15,
  -- [B7] decode raw long form idx16.
  mkCaseCode "ok/decode/raw-57-10" (makeStack 17) popRawLong16,
  -- [B7] decode raw long form idx255.
  mkCaseCode "ok/decode/raw-57-ff" (makeStack 256) popRawLong255,
  -- [B7] decode raw long form idx1 and short-branch semantics equivalent for same idx.
  mkCaseCode "ok/decode/long-eq-short-idx1" #[intV 100, intV 200] popRawPop1Long,
  -- [B8] decode adjacency check in raw stream.
  mkCaseCode "ok/decode/adjacent-pop1-over" (makeStack 3) popRawNeighborOver,

  -- [B11] gas exact short budget should succeed.
  mkGasCase "gas/exact/success-short" (makeStack 2) 1 popShortExactGas
    (oracleGasLimitsExact popShortExactGas),
  -- [B11] gas exact-minus-one short should fail.
  mkGasCase "gas/exact-minus-one/fail-short" (makeStack 2) 1 popShortGasMinusOne
    (oracleGasLimitsExact popShortGasMinusOne),
  -- [B11] gas exact long budget should succeed.
  mkGasCase "gas/exact/success-long" (makeStack 18) 16 popLongExactGas
    (oracleGasLimitsExact popLongExactGas),
  -- [B11] gas exact-minus-one long should fail.
  mkGasCase "gas/exact-minus-one/fail-long" (makeStack 18) 16 popLongGasMinusOne
    (oracleGasLimitsExact popLongGasMinusOne)
]

def suite : InstrSuite where
  id := popLongId
  unit := #[
    { name := "unit/encoding/short-idx0"
      run := do
        expectEncodeShortByte "encode/short/idx0" 0 0x30
        expectEncodeShortByte "encode/short/idx1" 1 0x31
        expectEncodeShortByte "encode/short/idx15" 15 0x3f
    }
    ,
    { name := "unit/encoding/long-idx16-and-idx255"
      run := do
        expectEncodeLongWord "encode/long/idx16" 16
        expectEncodeLongWord "encode/long/idx255" 255
    }
    ,
    { name := "unit/encoding/idx256-range-check-fails"
      run := do
        expectAssembleRangeErr "encode/idx256-fails" (popInstr 256)
    }
    ,
    { name := "unit/runtime/empty-underflow"
      run := do
        expectErr "runtime/empty" (runPopDirect 0 #[]) .stkUnd
    }
    ,
    { name := "unit/runtime/short-success"
      run := do
        expectOkStack "runtime/idx0-singleton" (runPopDirect 0 #[intV 11]) #[]
        expectOkStack "runtime/idx0-with-2"
          (runPopDirect 0 #[intV 10, intV 20])
          #[intV 10]
        expectOkStack "runtime/idx1" (runPopDirect 1 #[intV 10, intV 20]) #[intV 20]
        expectOkStack "runtime/idx2"
          (runPopDirect 2 #[intV 1, intV 2, intV 3, intV 4, intV 5])
          #[intV 1, intV 2, intV 5, intV 4]
        expectOkStack "runtime/type-mix-non-int"
          (runPopDirect 0 #[.null, intV 7, .cell Cell.empty])
          #[.null, intV 7]
    }
    ,
    { name := "unit/runtime/fallback-noop"
      run := do
        expectOkStack "runtime/fallback"
          (runPopFallback 2 #[intV 1, intV 2, intV 3, intV 4])
          #[intV 1, intV 2, intV 3, intV 4, intV 101]
    }
    ,
    { name := "unit/decode/short-vs-long-raw"
      run := do
        let s1 ← expectDecodeStep "decode/short-idx0" popRawShort0 (.pop 0) 8
        if s1.bitsRemaining ≠ 0 then
          throw (IO.userError s!"decode/short-idx0: expected end of stream, got {s1.bitsRemaining} bits")
        let _ ← expectDecodeStep "decode/long-idx16" popRawLong16 (.pop 16) 16
        pure ()
    }
    ,
    { name := "unit/decode/adjacency/pop1-over"
      run := do
        let _ ← expectDecodeStep "decode/adjacent-idx1" popRawNeighborOver (.pop 1) 8
        let _ ← expectDecodeStep "decode/adjacent-over" (Cell.mkOrdinary (natToBits 0x21 8) #[]) (.push 1) 8
        pure ()
    }
    ,
    { name := "unit/decode/alias/raw-short-vs-long-idx1"
      run := do
        let popShortCode : Cell := popRawShort1
        let s1 ← expectDecodeStep "decode/alias-short-1" popShortCode (.pop 1) 8
        if s1.bitsRemaining ≠ 0 then
          throw (IO.userError s!"decode/alias-short-1: expected empty tail, got {s1.bitsRemaining}")
        let longCode : Cell := popRawPop1Long
        let s2 ← expectDecodeStep "decode/alias-long-1" longCode (.pop 1) 16
        if s2.bitsRemaining ≠ 0 then
          throw (IO.userError s!"decode/alias-long-1: expected empty tail, got {s2.bitsRemaining}")
    }
    ,
    { name := "unit/decode/truncated-prefix-fails"
      run := do
        expectDecodeErr "decode/truncated-8" popRawTruncated8 .invOpcode
        match decodeCp0WithBits (Slice.ofCell popRawTruncated15) with
        | .ok (.nop, 8, _) => pure ()
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode/truncated-15: expected alias nop(8), got {reprStr instr} ({bits} bits)")
        | .error e =>
            throw (IO.userError s!"decode/truncated-15: expected alias nop(8), got error {e}")
    }
    ,
    { name := "unit/oracle-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle case count too small: {oracleCases.size} < 30")
    }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := fuzzSeedForInstr popLongId
      count := 500
      gen := genPopLongFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.POP_LONG
