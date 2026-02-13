import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.BLKPUSH

/-
INSTRUCTION: BLKPUSH

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [Normal path] Runtime success: `y < stack.size` then `x` pushes of `fetch(y)`.
   - Stack grows by exactly `x` values (all copies of the chosen source).
   - `fetch` reads by depth from top without mutation, so copied values preserve ordering.
   - `x` is not otherwise validated at runtime (execution loop runs exactly what the argument says).

2. [Error path] Runtime underflow: `y ≥ stack.size` (Lean: `if y < st.stack.size`, C++: `check_underflow_p(y)` which is strict depth > y).
   - Throws `.stkUnd` before any write mutation.

3. [Decoder boundary] Lower boundary aliasing: `0x5f00..0x5f0f` is decoded as `BLKDROP` (Lean and C++), so `BLKPUSH` starts at `0x5f10`.

4. [Decoder boundary] Upper boundary + round-trip encode range: `0x5f10..0x5fff` decodes as `BLKPUSH x y` with
   `1 ≤ x ≤ 15`, `0 ≤ y ≤ 15`; `0x5fff` maps to `x=15, y=15`.

5. [Decoder boundary] Adjacent opcode behavior: next opcode `0x6000` is **not** BLKPUSH (`PICK` in spec/registration), no implicit aliasing into BLKPUSH.

6. [Assembler encoding] `.blkPush x y` only accepts `1 ≤ x ≤ 15` and `0 ≤ y ≤ 15` in assembler.
   - Out-of-range params fail at assembly time (`.rangeChk`) before VM execution.

7. [Gas edge] Base gas behavior: no data-dependent / variable penalty in BLKPUSH semantics (`instrGas` only adds fixed decode-bit cost).
   - Exact `setGasLimit` + BLKPUSH budget should succeed.
   - Exact-minus-one budget should fail with out-of-gas before successful completion.

8. [Gas edge] No variable gas penalty branch (only base cost).

TOTAL BRANCHES: 8

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any category without a VM-runtime branch is explained below this map (assembler checks happen at assembly stage).
-/

private def blkPushId : InstrId := { name := "BLKPUSH" }

private def stack0 : Array Value := #[]

private def stack1 : Array Value := #[intV 17]

private def stack2 : Array Value := #[intV 7, intV 9]

private def stack3 : Array Value := #[intV (-2), intV 11, intV 23]

private def stack4 : Array Value := #[intV 1, intV 2, intV 3, intV 4]

private def stack9 : Array Value :=
  #[
    intV 101,
    intV 102,
    intV 103,
    intV 104,
    intV 105,
    intV 106,
    intV 107,
    intV 108,
    intV 109
  ]

private def stack10 : Array Value :=
  #[
    intV 201,
    intV 202,
    intV 203,
    intV 204,
    intV 205,
    intV 206,
    intV 207,
    intV 208,
    intV 209,
    intV 210
  ]

private def stack15 : Array Value :=
  #[
    intV 1,
    intV 2,
    intV 3,
    intV 4,
    intV 5,
    intV 6,
    intV 7,
    intV 8,
    intV 9,
    intV 10,
    intV 11,
    intV 12,
    intV 13,
    intV 14,
    intV 15
  ]

private def stack16 : Array Value :=
  #[
    intV 0,
    intV 1,
    intV 2,
    intV 3,
    intV 4,
    intV 5,
    intV 6,
    intV 7,
    intV 8,
    intV 9,
    intV 10,
    intV 11,
    intV 12,
    intV 13,
    intV 14,
    intV 15
  ]

private def mixedStack : Array Value :=
  #[
    intV 9,
    .null,
    .cell Cell.empty,
    .builder Builder.empty,
    intV (-3),
    .tuple #[]
  ]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blkPushId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkBlkPushCase
    (name : String)
    (stack : Array Value)
    (x : Nat)
  (y : Nat)
  (gasLimits : OracleGasLimits := {})
  (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (#[(.blkPush x y)] ) gasLimits fuel

private def mkRawCase
    (name : String)
    (stack : Array Value)
    (code : Nat)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blkPushId
    codeCell? := some (Cell.mkOrdinary (natToBits code 16) #[])
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def rawCode (x y : Nat) : Nat :=
  (0x5f00 + ((x <<< 4) + y))

private def exactGasBudget : Int :=
  computeExactGasBudget (.blkPush 3 1)

private def exactGasBudgetMinusOne : Int :=
  computeExactGasBudgetMinusOne (.blkPush 3 1)

private def oracleGasExactSuccess : OracleGasLimits :=
  { gasLimit := exactGasBudget
    gasMax := exactGasBudget
    gasCredit := 0 }

private def oracleGasExactMinusOne : OracleGasLimits :=
  { gasLimit := exactGasBudgetMinusOne
    gasMax := exactGasBudgetMinusOne
    gasCredit := 0 }

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genBlkPushFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 5
  if shape = 0 then
    let (stackChoice, rng2) := pickFromPool #[stack2, stack3, stack4, stack9, stack16, mixedStack] rng1
    let (x, rng3) := pickFromPool #[1, 2, 3, 7, 15] rng2
    let maxY := stackChoice.size - 1
    let (y, rng4) := randNat rng3 0 maxY
    ({ name := s!"fuzz/ok/success/{x}/{y}", instr := blkPushId, program := #[(.blkPush x y)], initStack := stackChoice }, rng4)
  else if shape = 1 then
    let (x, rng3) := pickFromPool #[1, 2, 4, 9, 15] rng1
    let (stackChoice, rng4) := pickFromPool #[stack4, stack9, stack10, stack15] rng3
    ({ name := s!"fuzz/err/underflow/{x}/size-{stackChoice.size}", instr := blkPushId, program := #[(.blkPush x (stackChoice.size))], initStack := stackChoice }, rng4)
  else if shape = 2 then
    let (x, rng2) := pickFromPool #[1, 2, 5, 10, 15] rng1
    let (y, rng3) := pickFromPool #[0, 1, 4, 7, 10, 15] rng2
    ({ name := s!"fuzz/err/underflow-empty/{x}/{y}", instr := blkPushId, program := #[(.blkPush x y)], initStack := stack0 }, rng3)
  else if shape = 3 then
    let (_x, rng2) := pickFromPool #[1, 2, 7, 11, 15] rng1
    let (code, rng3) := pickFromPool (#[0x5f0f, 0x5f10, 0x5fff, 0x6000]) rng2
    if code = 0x6000 then
      ({ name := "fuzz/raw/adjacent-pick", instr := blkPushId, codeCell? := some (Cell.mkOrdinary (natToBits 0x6000 16) #[]), initStack := #[intV 21, intV 0] }, rng3)
    else if code = 0x5f0f then
      ({ name := "fuzz/raw/adjacent-blkdrop", instr := blkPushId, codeCell? := some (Cell.mkOrdinary (natToBits code 16) #[]), initStack := stack16 }, rng3)
    else
      ({ name := s!"fuzz/raw/blkpush/{code}", instr := blkPushId, codeCell? := some (Cell.mkOrdinary (natToBits code 16) #[]), initStack := stack16 }, rng3)
  else
    let (x, rng2) := pickFromPool #[1, 3, 5, 9, 15] rng1
    let (y, rng3) := pickFromPool #[0, 1, 3, 7, 10] rng2
    let (extra, rng4) := randBool rng3
  if extra then
      let (base, rng5) := pickFromPool #[stack10, mixedStack, stack16] rng4
      ({ name := s!"fuzz/ok/boundary/{x}/{y}", instr := blkPushId, program := #[(.blkPush x y)], initStack := base }, rng5)
    else
      let y' : Nat := if y = 0 then 1 else y
      ({ name := s!"fuzz/err/size/{x}/{y}", instr := blkPushId, program := #[(.blkPush x y')], initStack := if y = 0 then stack1 else stack3 }, rng4)


private def decodeOk (code : Nat) (x y : Nat) : Bool :=
  match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits code 16) #[])) with
  | .ok (instr, bits, rest) =>
      bits = 16 && rest.bitsRemaining + rest.refsRemaining = 0 && instr == .blkPush x y
  | .error _ => false

private def decodeCheckBlkDrop (code : Nat) : Bool :=
  match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits code 16) #[])) with
  | .ok (instr, _, _) =>
      match instr with
      | .blkdrop 15 => True
      | _ => False
  | .error _ => False

/--
`decodeOk` and `decodeCheckBlkDrop` above are used only in unit tests; they assert decoder boundaries are stable.
-/

private def exactProgram : Array Instr :=
  #[.pushInt (.num exactGasBudget), .tonEnvOp .setGasLimit, .blkPush 3 1]

private def exactProgramMinusOne : Array Instr :=
  #[.pushInt (.num exactGasBudgetMinusOne), .tonEnvOp .setGasLimit, .blkPush 3 1]

def suite : InstrSuite where
  id := blkPushId
  unit := #[
    { name := "unit/asm/accept-range-min"
      run := do
        match assembleCp0 [ .blkPush 1 0 ] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"assemble x=1,y=0 failed: {e}") },
    { name := "unit/asm/accept-range-max"
      run := do
        match assembleCp0 [ .blkPush 15 15 ] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"assemble x=15,y=15 failed: {e}") },
    { name := "unit/asm/reject-x-0"
      run := do
        match assembleCp0 [ .blkPush 0 0 ] with
        | .ok _ => throw (IO.userError "assemble x=0 unexpectedly succeeded")
        | .error _ => pure () },
    { name := "unit/asm/reject-x-16"
      run := do
        match assembleCp0 [ .blkPush 16 0 ] with
        | .ok _ => throw (IO.userError "assemble x=16 unexpectedly succeeded")
        | .error _ => pure () },
    { name := "unit/asm/reject-y-16"
      run := do
        match assembleCp0 [ .blkPush 1 16 ] with
        | .ok _ => throw (IO.userError "assemble y=16 unexpectedly succeeded")
        | .error _ => pure () },
    { name := "unit/decode/alias-low-boundary-5f0f"
      run := do
        if decodeCheckBlkDrop 0x5f0f then
          pure ()
        else
          throw (IO.userError "decode 0x5f0f did not produce BLKDROP(15)") },
    { name := "unit/decode/roundtrip-min"
      run := do
        if decodeOk (rawCode 1 0) 1 0 then
          pure ()
        else
          throw (IO.userError "decode 0x5f10 was not BLKPUSH 1,0") },
    { name := "unit/decode/roundtrip-max"
      run := do
        if decodeOk (rawCode 15 15) 15 15 then
          pure ()
        else
          throw (IO.userError "decode 0x5fff was not BLKPUSH 15,15") }
  ]
  oracle := #[
    mkBlkPushCase "ok/top-copy-x1-y0" stack2 1 0, -- [B1]
    mkBlkPushCase "ok/second-copy-x1-y1" stack3 1 1, -- [B1]
    mkBlkPushCase "ok/deepest-copy-x1-y3" stack4 1 3, -- [B1]
    mkBlkPushCase "ok/top-multi-copy-x3-y0" stack16 3 0, -- [B1]
    mkBlkPushCase "ok/middle-copy-x5-y4" stack16 5 4, -- [B1]
    mkBlkPushCase "ok/top-copy-x15" stack16 15 0, -- [B1]
    mkBlkPushCase "ok/deepest-copy-x1-y15" stack16 1 15, -- [B1]
    mkBlkPushCase "ok/max-copy-x15-y15" stack16 15 15, -- [B1]
    mkBlkPushCase "ok/mixed-copy-x7-y0" mixedStack 7 0, -- [B1]
    mkBlkPushCase "ok/mixed-copy-x9-y2" mixedStack 9 2, -- [B1]
    mkBlkPushCase "ok/negative-copy-x2-y5" #[(intV (-7)), intV 99, intV (-2), intV 5, intV (-13), intV 21] 2 5, -- [B1]
    mkBlkPushCase "ok/size10-y9-x4" stack10 4 9, -- [B1]
    mkBlkPushCase "ok/size15-y0-x3" stack15 3 0, -- [B1]
    mkBlkPushCase "ok/size15-y14-x1" stack15 1 14, -- [B1]
    mkBlkPushCase "ok/size9-y8-x1" stack9 1 8, -- [B1]
    mkBlkPushCase "ok/size10-y0-x12" stack10 12 0, -- [B1]
    mkBlkPushCase "err/underflow/empty-y0" stack0 1 0, -- [B2]
    mkBlkPushCase "err/underflow/empty-y15" stack0 15 15, -- [B2]
    mkBlkPushCase "err/underflow/size1-y1" stack1 1 1, -- [B2]
    mkBlkPushCase "err/underflow/size2-y2" stack2 3 2, -- [B2]
    mkBlkPushCase "err/underflow/size4-y4" stack4 2 4, -- [B2]
    mkBlkPushCase "err/underflow/size4-y7" stack4 5 7, -- [B2]
    mkBlkPushCase "err/underflow/size9-y9" stack9 1 9, -- [B2]
    mkBlkPushCase "err/underflow/size10-y10" stack10 10 10, -- [B2]
    mkBlkPushCase "err/underflow/size15-y15" stack15 1 15, -- [B2]
    mkBlkPushCase "err/underflow/size15-y15-x7" stack15 7 15, -- [B2]
    mkRawCase "decode/alias-low-boundary-5f0f" stack16 0x5f0f, -- [B3]
    mkRawCase "decode/min-boundary-5f10-y0" stack2 0x5f10, -- [B4]
    mkRawCase "decode/adjacent-low-5f12" stack16 0x5f12, -- [B4]
    mkRawCase "decode/mid-boundary-5f35" stack16 0x5f35, -- [B4]
    mkRawCase "decode/max-boundary-5fff" stack16 0x5fff, -- [B4]
    mkRawCase "decode/max-boundary-underflow" stack15 0x5fff, -- [B2]
    mkRawCase "decode/adjacent-opcode-6000" stack2 0x6000, -- [B5]
    mkRawCase "decode/adjacent-opcode-6000-underflow" stack0 0x6000, -- [B5]
    mkCase "gas/exact-success" stack3 exactProgram (gasLimits := oracleGasExactSuccess), -- [B7]
    mkCase "gas/exact-minus-one-out-of-gas" stack3 exactProgramMinusOne (gasLimits := oracleGasExactMinusOne) -- [B8]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr blkPushId
      count := 500
      gen := genBlkPushFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.BLKPUSH
