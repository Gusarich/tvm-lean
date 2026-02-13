import Std
import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.NIP

/-
INSTRUCTION: NIP

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime success path: `.pop 1` executes `swap 0 1` then `pop`.
   - The top item remains, and the second-from-top item is removed.
   - No type/range validation is performed.
2. [B2] Runtime stack-shape path: lower stack prefix values are preserved when
   removing the second-from-top item from depth >= 3.
3. [B3] Runtime error path: underflow (`stkUnd`) when stack size < 2.
4. [B4] Dispatch branch: this instruction is handled only by
   `execInstrStackPop` (when the opcode decodes to `.pop _`) and falls through
   for other instructions.
5. [B5] Assembler fixed-form encoding/decoding:
   - `idx = 1` encodes as short opcode `0x31`.
   - `idx = 0..15` use short opcodes `0x30..0x3f`.
6. [B6] Assembler long-form/range branch:
   - `idx = 16..255` encodes as short-like prefix `0x57` + `idx`.
   - `idx > 255` fails with `rangeChk`.
7. [B7] Decoder branch and opcode adjacency:
   - `0x31 => .pop 1`, `0x30 => .pop 0`, `0x32 => .pop 2`, `0x3f => .pop 15`,
     and `0x57 nn => .pop nn`.
8. [B8] Decoder malformed/truncated branch:
   - `0x40` and truncated forms (e.g. `0x57` without second byte) must fail as
     `invOpcode`.
9. [B9] Gas accounting:
   - No variable gas is added by this instruction; only base `instrGas`
     (`gasPerInstr + totBits`) applies.
   - Verify exact-budget success and exact-budget-minus-one failure.

TOTAL BRANCHES: 9

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def nipId : InstrId := { name := "NIP" }

private def nipInstr : Instr := .pop 1

private def dispatchSentinel : Int := 49321

private def nipExactGas : Int :=
  computeExactGasBudget nipInstr

private def nipExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne nipInstr

private def nipGasExact : OracleGasLimits :=
  oracleGasLimitsExact nipExactGas

private def nipGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne nipExactGasMinusOne

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[nipInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := nipId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRawCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := nipId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw4 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 4) #[]

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr)
    (expectedBits : Nat := 8) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error, got {reprStr instr} / {bits}")

private def expectAssembleErr
    (label : String)
    (instr : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def runNIPDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPop nipInstr stack

private def cellA : Cell := Cell.mkOrdinary (natToBits 0xa5 8) #[]
private def cellB : Cell := Cell.mkOrdinary (natToBits 0x5a 8) #[cellA]
private def fullSliceA : Slice := Slice.ofCell cellA
private def fullSliceB : Slice := Slice.ofCell cellB
private def builderA : Builder := Builder.empty
private def emptyTuple : Value := .tuple #[]

private def noiseA : Array Value :=
  #[.null, .cell cellA, .slice fullSliceA, .builder builderA, intV 17]

private def noiseB : Array Value :=
  #[.cell cellB, .slice fullSliceB, emptyTuple, .cont (.quit 0), intV (-5)]

private def stack16 : Array Value :=
  Array.range 16 |>.map fun i => intV i.toInt

private def stack17 : Array Value :=
  Array.range 17 |>.map fun i => intV i.toInt

private def nipCode : Cell := raw8 0x31
private def dropCode : Cell := raw8 0x30
private def pop2Code : Cell := raw8 0x32
private def pop15Code : Cell := raw8 0x3f
private def pop16Code : Cell := raw16 0x5710
private def invalid40Code : Cell := raw8 0x40
private def truncated4Code : Cell := raw4 0x3
private def truncated57Code : Cell := raw8 0x57

private def pickNipValue (rng0 : StdGen) : Value × StdGen :=
  let (mode, rng1) := randNat rng0 0 11
  if mode = 0 then
    (intV 0, rng1)
  else if mode = 1 then
    (intV 1, rng1)
  else if mode = 2 then
    (intV (-1), rng1)
  else if mode = 3 then
    (intV maxInt257, rng1)
  else if mode = 4 then
    (intV minInt257, rng1)
  else if mode = 5 then
    (.null, rng1)
  else if mode = 6 then
    (.cell cellA, rng1)
  else if mode = 7 then
    (.tuple #[], rng1)
  else if mode = 8 then
    (.slice fullSliceA, rng1)
  else if mode = 9 then
    (.cont (.quit 0), rng1)
  else
    let (n, rng2) := pickSigned257ish rng1
    (intV n, rng2)

private def genNipStack (size : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  let mut i : Nat := 0
  while i < size do
    let (v, rng') := pickNipValue rng
    out := out.push v
    rng := rng'
    i := i + 1
  pure (out, rng)

private def genNipFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    let (a, rng2) := pickSigned257ish rng1
    let (b, rng3) := pickSigned257ish rng2
    let (tag, rng4) := randNat rng3 0 999_999
    ({
      name := s!"fuzz/ok/size2-int-a-{tag}",
      instr := nipId,
      program := #[nipInstr],
      initStack := #[intV a, intV b]
    }, rng4)
  else if shape = 1 then
    let (a, rng2) := pickSigned257ish rng1
    let (tag, rng3) := randNat rng2 0 999_999
    ({
      name := s!"fuzz/ok/size2-null-top-{tag}",
      instr := nipId,
      program := #[nipInstr],
      initStack := #[.null, intV a]
    }, rng3)
  else if shape = 2 then
    let (stack, rng2) := genNipStack 3 rng1
    let (tag, rng3) := randNat rng2 0 999_999
    ({
      name := s!"fuzz/ok/size3-random-{tag}",
      instr := nipId,
      program := #[nipInstr],
      initStack := stack
    }, rng3)
  else if shape = 3 then
    let (stack, rng2) := genNipStack 4 rng1
    let (tag, rng3) := randNat rng2 0 999_999
    ({
      name := s!"fuzz/ok/size4-random-{tag}",
      instr := nipId,
      program := #[nipInstr],
      initStack := stack
    }, rng3)
  else if shape = 4 then
    let (stack, rng2) := genNipStack 6 rng1
    let (tag, rng3) := randNat rng2 0 999_999
    ({
      name := s!"fuzz/ok/size6-random-{tag}",
      instr := nipId,
      program := #[nipInstr],
      initStack := stack
    }, rng3)
  else if shape = 5 then
    let (a, rng2) := pickInt257Boundary rng1
    let (b, rng3) := pickInt257Boundary rng2
    let (tag, rng4) := randNat rng3 0 999_999
    ({
      name := s!"fuzz/ok/size16-heterogeneous-{tag}",
      instr := nipId,
      program := #[nipInstr],
      initStack := stack16 ++ #[intV a, intV b]
    }, rng4)
  else if shape = 6 then
    let (tag, rng2) := randNat rng1 0 999_999
    ({
      name := s!"fuzz/ok/size17-boundary-{tag}",
      instr := nipId,
      program := #[nipInstr],
      initStack := stack17
    }, rng2)
  else if shape = 7 then
    let (tag, rng2) := randNat rng1 0 999_999
    ({
      name := s!"fuzz/err/underflow/empty-{tag}",
      instr := nipId,
      program := #[nipInstr],
      initStack := #[]
    }, rng2)
  else if shape = 8 then
    let (a, rng2) := pickSigned257ish rng1
    let (tag, rng3) := randNat rng2 0 999_999
    ({
      name := s!"fuzz/err/underflow/one-item-int-{tag}",
      instr := nipId,
      program := #[nipInstr],
      initStack := #[intV a]
    }, rng3)
  else if shape = 9 then
    let (tag, rng2) := randNat rng1 0 999_999
    ({
      name := s!"fuzz/err/underflow/one-item-null-{tag}",
      instr := nipId,
      program := #[nipInstr],
      initStack := #[.null]
    }, rng2)
  else if shape = 10 then
    let (tag, rng2) := randNat rng1 0 999_999
    ({
      name := s!"fuzz/err/underflow/one-item-cell-{tag}",
      instr := nipId,
      program := #[nipInstr],
      initStack := #[.cell cellA]
    }, rng2)
  else
    let (tag, rng2) := randNat rng1 0 999_999
    ({
      name := s!"fuzz/err/underflow/one-item-slice-{tag}",
      instr := nipId,
      program := #[nipInstr],
      initStack := #[.slice fullSliceA]
    }, rng2)


def suite : InstrSuite where
  id := nipId
  unit := #[
    { name := "unit/runtime/dispatch/execute-pop1-two-items"
      run := do
        expectOkStack "unit/runtime/dispatch/ok" (runNIPDirect #[intV 9, intV 4]) #[intV 4]
    },
    { name := "unit/runtime/dispatch/skip-non-pop-instruction"
      run := do
        let res := runHandlerDirectWithNext execInstrStackPop (.push 0) (VM.push (intV dispatchSentinel)) #[]
        expectOkStack "unit/runtime/dispatch/skip" res #[intV dispatchSentinel]
    },
    { name := "unit/asmdecode/encode-fixed-pop1"
      run := do
        match assembleCp0 [nipInstr] with
        | .ok code =>
            expectDecodeOk "unit/nip/encode" code (.pop 1) 8
        | .error e =>
            throw (IO.userError s!"unit/nip/encode: assemble failed with {e}")
    },
    { name := "unit/asmdecode/encode-boundaries"
      run := do
        match assembleCp0 [(.pop 0)] with
        | .ok code =>
            expectDecodeOk "unit/nip/encode-pop0" code (.pop 0) 8
        | .error e =>
            throw (IO.userError s!"unit/nip/encode-pop0: assemble failed with {e}")
        expectDecodeOk "unit/nip/encode-pop15" (raw8 0x3f) (.pop 15) 8
        match assembleCp0 [(.pop 16)] with
        | .ok code =>
            expectDecodeOk "unit/nip/encode-pop16" code (.pop 16) 16
        | .error e =>
            throw (IO.userError s!"unit/nip/encode-pop16: assemble failed with {e}")
    },
    { name := "unit/asmdecode/decode-failures"
      run := do
        expectAssembleErr "unit/nip/assemble-pop256" (.pop 256) .rangeChk
        expectDecodeErr "unit/nip/decode-op40" invalid40Code .invOpcode
        expectDecodeErr "unit/nip/decode-truncated-57" truncated57Code .invOpcode
        expectDecodeErr "unit/nip/decode-truncated-4bit" truncated4Code .invOpcode
    },
    { name := "unit/asmdecode/raw-opcode-boundaries"
      run := do
        expectDecodeOk "unit/nip/raw-pop0" dropCode (.pop 0)
        expectDecodeOk "unit/nip/raw-pop1" nipCode (.pop 1)
        expectDecodeOk "unit/nip/raw-pop2" pop2Code (.pop 2)
        expectDecodeOk "unit/nip/raw-pop15" pop15Code (.pop 15)
        expectDecodeOk "unit/nip/raw-pop16" pop16Code (.pop 16) 16
    }
  ]
  oracle := #[
    -- [B1]
    mkCase "oracle/ok/basic/pos-pos" #[intV 17, intV 42],
    -- [B1]
    mkCase "oracle/ok/basic/neg-neg" #[intV (-3), intV (-11)],
    -- [B1]
    mkCase "oracle/ok/basic/zero" #[intV 0, intV 0],
    -- [B1]
    mkCase "oracle/ok/basic/max-boundary" #[intV maxInt257, intV 0],
    -- [B1]
    mkCase "oracle/ok/basic/min-boundary" #[intV minInt257, intV 7],
    -- [B1]
    mkCase "oracle/ok/basic/repeated-top" #[intV 123, intV 123],
    -- [B1]
    mkCase "oracle/ok/basic/mixed-null-top" #[.null, intV 99],
    -- [B1]
    mkCase "oracle/ok/basic/mixed-cell-top" #[.cell cellA, intV 5],
    -- [B1]
    mkCase "oracle/ok/basic/mixed-slice-top" #[.slice fullSliceA, intV 1],
    -- [B1]
    mkCase "oracle/ok/basic/mixed-builder-top" #[.builder builderA, intV (-17)],

    -- [B2]
    mkCase "oracle/ok/size3-prefix-preserved" #[intV 1, intV 2, intV 3],
    -- [B2]
    mkCase "oracle/ok/size4-prefix-preserved" #[.null, .cell cellA, intV 55, intV 77],
    -- [B2]
    mkCase "oracle/ok/size5-prefix-preserved" #[.null, intV 10, .tuple #[], .slice fullSliceB, intV 77],
    -- [B2]
    mkCase "oracle/ok/size6-prefix-preserved" #[.cell cellA, intV 1, .builder builderA, .tuple #[], intV 5, intV 9],
    -- [B2]
    mkCase "oracle/ok/size7-prefix-preserved" #[.cont (.quit 0), intV 2, .null, .cell cellB, intV 3, .tuple #[], intV 13],
    -- [B2]
    mkCase "oracle/ok/size16-shape" stack16,
    -- [B2]
    mkCase "oracle/ok/size17-shape" stack17,

    -- [B3]
    mkCase "oracle/err/underflow/empty-stack" #[],
    -- [B3]
    mkCase "oracle/err/underflow/single-int" #[intV 1],
    -- [B3]
    mkCase "oracle/err/underflow/single-null" #[.null],
    -- [B3]
    mkCase "oracle/err/underflow/single-cell" #[.cell cellA],
    -- [B3]
    mkCase "oracle/err/underflow/single-slice" #[.slice fullSliceA],

    -- [B4, B5]
    mkCase "oracle/ok/dispatch-target-pop1" #[intV 8, intV 9],

    -- [B5]
    mkCase "oracle/ok/assemble-pop1" #[intV 1, intV 0],
    -- [B5]
    mkCase "oracle/ok/assemble-pop2" #[intV 7, intV 8], #[.pop 2],
    -- [B5]
    mkCase "oracle/ok/assemble-pop15" #[intV 15, intV 16], #[.pop 15],

    -- [B6]
    mkCase "oracle/ok/assemble-pop16" #[intV 0, intV 1], #[.pop 16],
    -- [B6]
    mkCase "oracle/err/assemble-pop256-range" #[intV 1, intV 2], #[.pop 256],

    -- [B7]
    mkRawCase "oracle/raw/0x31-pop1" #[intV 5, intV 6] nipCode,
    -- [B7]
    mkRawCase "oracle/raw/0x30-pop0" #[intV 9] dropCode,
    -- [B7]
    mkRawCase "oracle/raw/0x32-pop2" #[intV 9, intV 10, intV 11] pop2Code,
    -- [B7]
    mkRawCase "oracle/raw/0x3f-pop15" stack16 pop15Code,
    -- [B7]
    mkRawCase "oracle/raw/0x57-10-pop16" stack17 pop16Code,

    -- [B8]
    mkRawCase "oracle/err/raw/opcode-40" #[intV 1, intV 2] invalid40Code,
    -- [B8]
    mkRawCase "oracle/err/raw/truncated-0x57" #[intV 1, intV 2] truncated57Code,
    -- [B8]
    mkRawCase "oracle/err/raw/truncated-4bit" #[intV 1, intV 2] truncated4Code,

    -- [B9]
    mkCase "oracle/gas/exact-budget-succeeds"
      #[intV 8, intV 9]
      #[nipInstr]
      nipGasExact,
    -- [B9]
    mkCase "oracle/gas/exact-minus-one-out-of-gas"
      #[intV 8, intV 9]
      #[nipInstr]
      nipGasExactMinusOne
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr nipId
      count := 500
      gen := genNipFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.NIP
