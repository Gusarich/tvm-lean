import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.NOP

/-
BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [Runtime: identity semantics, single no-op] - when executing `.nop`, stack is unchanged for any non-trivial input shape.
2. [Runtime: identity semantics, mixed stack shapes] - `.nop` also preserves non-int values and heterogeneous stacks.
3. [Runtime: identity semantics, non-empty stack] - no underflow/type path exists in `.nop`; same-stack behavior applies to all stack sizes.
4. [Runtime: fall-through] - execution reaches the next instruction when `.nop` is in-program and does not jump/return/throw.
5. [Assembler: fixed-width encoding] - `.nop` has only one valid constructor form and always encodes to the 8-bit family entry with prefix 0.
6. [Assembler: no-op parameter range] - no range checks/overflow branches exist because `.nop` takes no arguments.
7. [Decoder boundary: exact-byte decode] - `0x00` decodes as `.nop`, consuming 8 bits.
8. [Decoder sequencing] - decode consumes exactly 8 bits for fixed width; trailing bits are interpreted by subsequent decoding.
9. [Decoder boundary: neighboring opcode] - values not equal to `0x00` decode to other stack/flow opcodes (e.g. `0x01` → `.swap`).
10. [Decoder edge: too-short opcodes] - insufficient bits before fixed-width match yields `.invOpcode`.
11. [Decoder edge: unassigned/invalid opcode] - unknown 8-bit entries (e.g. `0xFF`) return `.invOpcode`.
12. [Gas accounting: no-op baseline] - exact gas check succeeds when budget is at least `gasPerInstr + 8` plus execution wrapper overhead (as `computeExactGasBudget .nop`).
13. [Gas edge] - `computeExactGasBudgetMinusOne` for `.nop` fails with out-of-gas.

TOTAL BRANCHES: 13

Any branch with no branches:
- Assembler range checks: `.nop` has no operands, therefore there is no argument-dependent branch to test.

Each oracle test below is tagged with the branch IDs it covers.
-/

private def nopId : InstrId := { name := "NOP" }
private def nopInstr : Instr := .nop

private def nopSetGasExact : Int :=
  computeExactGasBudget nopInstr

private def nopSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne nopInstr

private def nopOpcode : Nat := 0
private def swapOpcode : Nat := 1
private def invOpcode : Nat := 255

private def nopCode8 : BitString :=
  natToBits nopOpcode 8

private def swapCode8 : BitString :=
  natToBits swapOpcode 8

private def invCode8 : BitString :=
  natToBits invOpcode 8

private def mkCase
    (name : String)
    (initStack : Array Value)
    (program : Array Instr := #[.nop])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := nopId
    program := program
    initStack := initStack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRawCase
    (name : String)
    (code : Cell)
    (initStack : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := nopId
    codeCell? := some code
    initStack := initStack
    gasLimits := gasLimits
    fuel := fuel }

private def nopRawCode : Cell :=
  Cell.mkOrdinary nopCode8 #[]

private def nopNopRawCode : Cell :=
  Cell.mkOrdinary (nopCode8 ++ nopCode8) #[]

private def nopSwapRawCode : Cell :=
  Cell.mkOrdinary (nopCode8 ++ swapCode8) #[]

private def swapRawCode : Cell :=
  Cell.mkOrdinary swapCode8 #[]

private def invRawCode : Cell :=
  Cell.mkOrdinary invCode8 #[]

private def nopInvRawCode : Cell :=
  Cell.mkOrdinary (nopCode8 ++ invCode8) #[]

private def nopTrunc4Code : Cell :=
  Cell.mkOrdinary (nopCode8.take 4) #[]

private def nopTrunc7Code : Cell :=
  Cell.mkOrdinary (nopCode8.take 7) #[]

private def genNopFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  match shape with
  | 0 =>
      let (x, rng2) := pickSigned257ish rng1
      (mkCase "fuzz/shape/0/single-signed" #[intV x], rng2)
  | 1 =>
      let (x, rng2) := pickSigned257ish rng1
      let (y, rng3) := pickSigned257ish rng2
      (mkCase "fuzz/shape/1/pair-signed" #[intV x, intV y], rng3)
  | 2 =>
      let (x, rng2) := pickInt257Boundary rng1
      let (y, rng3) := pickInt257Boundary rng2
      (mkCase "fuzz/shape/2/boundary-pair" #[intV x, intV y], rng3)
  | 3 =>
      let (x, rng2) := pickSigned257ish rng1
      (mkCase "fuzz/shape/3/mixed" #[.null, intV x, .cell Cell.empty, .builder Builder.empty], rng2)
  | 4 =>
      (mkRawCase "fuzz/shape/4/raw-nop" nopRawCode, rng1)
  | 5 =>
      let (x, rng2) := pickSigned257ish rng1
      (mkRawCase "fuzz/shape/5/raw-nop-swap" nopSwapRawCode #[intV x, intV 7], rng2)
  | 6 =>
      (mkRawCase "fuzz/shape/6/raw-truncated-7bits" nopTrunc7Code #[intV 99], rng1)
  | 7 =>
      (mkRawCase "fuzz/shape/7/raw-unassigned" invRawCode, rng1)
  | 8 =>
      (mkCase "fuzz/shape/8/gas-exact" #[]
        #[.pushInt (.num nopSetGasExact), .tonEnvOp .setGasLimit, .nop], rng1)
  | _ =>
      (mkCase "fuzz/shape/9/gas-minus-one" #[]
        #[.pushInt (.num nopSetGasExactMinusOne), .tonEnvOp .setGasLimit, .nop], rng1)

/--
NOP unit checks for assembler/decoder contract on the fixed 8-bit encoding.
-/
private def failUnit (msg : String) : IO α :=
  throw (IO.userError msg)

private def toBits (c : Cell) : BitString :=
  c.bits

def suite : InstrSuite where
  id := nopId
  unit := #[
    { name := "unit/asm/nop-is-00"
      run := do
        let c ←
        match assembleCp0 [nopInstr] with
        | .ok c => pure c
        | .error e => failUnit s!"assemble failed: {reprStr e}"
        if c.bits != nopCode8 then
          failUnit s!"assemble/nop: unexpected bits {reprStr (toBits c)}"
    },
    { name := "unit/decode/nop-raw-00"
      run := do
        match decodeCp0WithBits (Slice.ofCell nopRawCode) with
        | .ok (instr, totBits, _) =>
            if instr != nopInstr then
              failUnit s!"decode/nop: expected .nop, got {reprStr instr}"
            if totBits != 8 then
              failUnit s!"decode/nop: expected totBits=8, got {totBits}"
        | .error e =>
            failUnit s!"decode/nop: expected success, got {reprStr e}"
    },
    { name := "unit/decode/truncated-4bits-invOpcode"
      run := do
        match decodeCp0WithBits (Slice.ofCell nopTrunc4Code) with
        | .error .invOpcode => pure ()
        | .error e => failUnit s!"decode/truncated-4bits: expected invOpcode, got {reprStr e}"
        | .ok (instr, totBits, _) =>
            failUnit s!"decode/truncated-4bits: expected error, got {reprStr instr} (totBits={totBits})" }
  ]
  oracle := #[
    mkCase "oracle/ok/empty-stack" #[] , -- [B1]
    mkCase "oracle/ok/single/int-zero" #[intV 0], -- [B2]
    mkCase "oracle/ok/single/int-one" #[intV 1], -- [B2]
    mkCase "oracle/ok/single/int-minus-one" #[intV (-1)], -- [B2]
    mkCase "oracle/ok/single/int-max" #[intV maxInt257], -- [B3]
    mkCase "oracle/ok/single/int-min" #[intV minInt257], -- [B3]
    mkCase "oracle/ok/single/int-max-plus-one" #[intV (maxInt257 - 1)], -- [B3]
    mkCase "oracle/ok/single/int-min-plus-one" #[intV (minInt257 + 1)], -- [B3]
    mkCase "oracle/ok/pair/pos-pos" #[intV 17, intV 5], -- [B3]
    mkCase "oracle/ok/pair/neg-pos" #[intV (-17), intV 5], -- [B3]
    mkCase "oracle/ok/pair/neg-neg" #[intV (-17), intV (-5)], -- [B3]
    mkCase "oracle/ok/mixed/null-only" #[.null], -- [B4]
    mkCase "oracle/ok/mixed/cell-only" #[.cell Cell.empty], -- [B4]
    mkCase "oracle/ok/mixed/builder-only" #[.builder Builder.empty], -- [B4]
    mkCase "oracle/ok/mixed/tuple-only" #[.tuple #[]], -- [B4]
    mkCase "oracle/ok/mixed/cont-only" #[.cont (.quit 0)], -- [B4]
    mkCase "oracle/ok/mixed/short-stack" #[.null, intV 7, .cell Cell.empty], -- [B4]
    mkCase "oracle/ok/mixed/mid-stack" #[intV 42, .null, .builder Builder.empty, .tuple #[], .cell Cell.empty], -- [B4]
    mkCase "oracle/ok/mixed/deep-stack-16" #[
      intV 1, intV 2, .null, .cell Cell.empty, intV 3, .builder Builder.empty,
      intV 4, .tuple #[], intV 5, .cont (.quit 0), intV 6, .null, intV 7,
      .cell Cell.empty, intV 8, .builder Builder.empty
    ], -- [B5]
    mkCase "oracle/ok/mixed/deep-stack-empty-nulls" #[
      .null, .null, .null, .null, intV 0, intV 1, intV 2, .null,
      .cell Cell.empty, .cell Cell.empty, .builder Builder.empty, intV 3, .cont (.quit 0),
      .tuple #[], .tuple #[], intV 4, .null
    ], -- [B5]
    mkCase "oracle/ok/fallthrough/add" #[intV 7, intV 5] #[.nop, .add], -- [B6]
    mkCase "oracle/ok/fallthrough/add" #[intV 11, intV 22] #[.nop, .add], -- [B6]
    mkRawCase "oracle/raw/decode/00-to-nop" nopRawCode, -- [B7]
    mkRawCase "oracle/raw/decode/00-00" nopNopRawCode, -- [B8]
    mkRawCase "oracle/raw/decode/00-01" nopSwapRawCode #[intV 11, intV 22], -- [B8]
    mkRawCase "oracle/raw/decode/01-1" swapRawCode #[intV 7, intV 9], -- [B9]
    mkRawCase "oracle/raw/decode/01-underflow" swapRawCode #[], -- [B9]
    mkRawCase "oracle/raw/decode/ff-only" invRawCode #[], -- [B11]
    mkRawCase "oracle/raw/decode/00-ff" nopInvRawCode #[], -- [B11]
    mkRawCase "oracle/raw/decode/truncated-4" nopTrunc4Code #[intV 1], -- [B10]
    mkRawCase "oracle/raw/decode/truncated-7" nopTrunc7Code #[intV 2], -- [B10]
    mkCase "oracle/gas/exact-cost-succeeds" #[]
      #[.pushInt (.num nopSetGasExact), .tonEnvOp .setGasLimit, .nop], -- [B12]
    mkCase "oracle/gas/exact-minus-one" #[]
      #[.pushInt (.num nopSetGasExactMinusOne), .tonEnvOp .setGasLimit, .nop], -- [B13]
    mkCase "oracle/runtime/fallthrough-nop-with-noise" #[intV 3, intV 9] #[.nop, .nop, .add], -- [B6]
    mkRawCase "oracle/raw/decode/truncated-7-mixed" nopTrunc7Code #[.null, intV 1], -- [B10]
    mkRawCase "oracle/raw/decode/00-00-01" (Cell.mkOrdinary (nopCode8 ++ nopCode8 ++ swapCode8) #[]) #[intV 4, intV 5], -- [B8]
    mkRawCase "oracle/raw/decode/00-ff-noise" nopInvRawCode #[.cell Cell.empty] -- [B11]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr nopId
      count := 500
      gen := genNopFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.NOP
