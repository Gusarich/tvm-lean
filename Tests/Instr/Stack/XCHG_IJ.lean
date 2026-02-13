import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.XCHG_IJ

/-
INSTRUCTION: XCHG_IJ

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Normal path — valid `xchg` encoding/decoded arguments (`x != 0`, `x < y`) with `y < stack.size` must perform a swap.
   - Lean: `execInstrStackXchg` checks `x=0 ∨ y ≤ x`, then `y < st.stack.size`, then `VM.swap x y`.
   - C++: `exec_xchg` throws `inv_opcode` for invalid args, checks `stack.check_underflow_p(y)`, then `swap(stack[x], stack[y])`.
   - Expected effect is a pure swap and stack size unchanged.

2. [B2] Runtime invalid args branch — `x = 0` must throw `invOpcode`.
   - Lean: immediate argument guard failure.
   - C++: same guard (`if (!x || x >= y) throw inv_opcode`).

3. [B3] Runtime invalid args branch — `x >= y` must throw `invOpcode`.
   - Lean: argument guard failure when `y ≤ x`.
   - C++: same as above.

4. [B4] Runtime underflow branch — `y` beyond stack depth throws `stkUnd`.
   - Lean: only checks `y < st.stack.size`, so any `y` out of range fails with stack underflow.
   - C++: `stack.check_underflow_p(y)` with same depth condition.

5. [B5] Assembler encoding range errors for invalid constructors.
   - Lean assembler `encodeTupleInstr`/`Asm/Cp0`: `.xchg x y` accepts only `0 < x`, `x < y`, `x ≤ 15`, `y ≤ 15`.
   - Out-of-range and invalid relations fail at assemble time with `.rangeChk`.

6. [B6] Decode-path branch for malformed/truncated 8-bit prefix `0x10` and 15-bit variant.
   - CP0 decoder takes `0x10` then consumes 8 bits for args; missing trailing bits should fail with `invOpcode`.

7. [B7] Gas edge — exact gas success/failure.
   - `XCHG_IJ` gas from runtime tables is base cost only (`26` for 16-bit form), no variable penalties.
   - Test exact budget and exact-minus-one budget by preloading gas with `setGasLimit` and executing swap.

TOTAL BRANCHES: 7

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer. Gas branch coverage is base-cost only; no variable penalty path exists.
-/

private def xchgIjId : InstrId :=
  { name := "XCHG_IJ" }

private def xchgCode (x : Nat) (y : Nat) : Cell :=
  Cell.mkOrdinary (natToBits (0x1000 + ((x <<< 4) + y)) 16) #[]

private def xchgTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0x10 8) #[]

private def xchgTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits ((0x1012 : Nat) >>> 1) 15) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.xchg 1 2])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xchgIjId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xchgIjId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def xchgSetGasExact : Int :=
  computeExactGasBudget (.xchg 1 2)

private def xchgSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.xchg 1 2)

private def stack16Base : Array Value :=
  #[
    intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8,
    intV 9, intV 10, intV 11, intV 12, intV 13, intV 14, intV 15, intV 16
  ]

private def pickFuzzToken (rng : StdGen) : Value × StdGen :=
  let (k, rng1) := randNat rng 0 8
  match k with
  | 0 => (intV 0, rng1)
  | 1 => (intV 1, rng1)
  | 2 => (intV (-1), rng1)
  | 3 => (intV maxInt257, rng1)
  | 4 => (intV minInt257, rng1)
  | 5 => (.null, rng1)
  | 6 => (.cell Cell.empty, rng1)
  | 7 => (.tuple #[], rng1)
  | _ => (.cont (.quit 0), rng1)

private def randomValueStack (n : Nat) (rng0 : StdGen) : Array Value × StdGen :=
  Id.run do
    let mut out : Array Value := #[]
    let mut rng := rng0
    for _ in [0:n] do
      let (v, rng') := pickFuzzToken rng
      out := out.push v
      rng := rng'
    return (out, rng)

private def genXchgIjFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 8
  if shape = 0 then
    let (x, rng2) := randNat rng1 1 14
    let (delta, rng3) := randNat rng2 1 (15 - x)
    let y : Nat := x + delta
    let (extra, rng4) := randNat rng3 0 2
    let (stack, rng5) := randomValueStack (y + 1 + extra) rng4
    (mkCase s!"fuzz/ok/x{x}-y{y}" stack (#[.xchg x y]), rng5)
  else if shape = 1 then
    let (x, rng2) := randNat rng1 1 14
    let (delta, rng3) := randNat rng2 1 (15 - x)
    let y : Nat := x + delta
    let (depth, rng4) := randNat rng3 0 y
    let (stack, rng5) := randomValueStack depth rng4
    (mkCase s!"fuzz/underflow/x{x}-y{y}" stack (#[.xchg x y]), rng5)
  else if shape = 2 then
    let (x, rng2) := randNat rng1 1 14
    let (y, rng3) := randNat rng2 0 x
    let (extra, rng4) := randNat rng3 1 2
    let (stack, rng5) := randomValueStack (y + extra) rng4
    (mkCaseCode s!"fuzz/raw-runtime-invalid/x{x}-y{y}" stack (xchgCode x y), rng5)
  else if shape = 3 then
    let (kind, rng2) := randNat rng1 0 4
    let program : Array Instr :=
      if kind = 0 then
        #[(.xchg 0 1)]
      else if kind = 1 then
        #[(.xchg 1 1)]
      else if kind = 2 then
        #[(.xchg 16 1)]
      else if kind = 3 then
        #[(.xchg 1 16)]
      else
        #[(.xchg 16 16)]
    let (depth, rng3) := randNat rng2 0 4
    let (stack, rng4) := randomValueStack depth rng3
    (mkCase s!"fuzz/asm-invalid/{kind}" stack program, rng4)
  else if shape = 4 then
    let (truncCase, rng2) := randNat rng1 0 1
    let (depth, rng3) := randNat rng2 0 2
    let (stack, rng4) := randomValueStack depth rng3
    if truncCase = 0 then
      (mkCaseCode "fuzz/decode/truncated-8" stack xchgTruncated8Code, rng4)
    else
      (mkCaseCode "fuzz/decode/truncated-15" stack xchgTruncated15Code, rng4)
  else if shape = 5 then
    let (tight, rng2) := randNat rng1 0 1
    let budget : Int := if tight = 0 then xchgSetGasExact else xchgSetGasExactMinusOne
    let (stack, rng3) := randomValueStack 3 rng2
    (mkCase
      (if tight = 0 then "fuzz/gas/exact" else "fuzz/gas/exact-minus-one")
      stack
      #[.pushInt (.num budget), .tonEnvOp .setGasLimit, .xchg 1 2], rng3)
  else if shape = 6 then
    let (x, rng2) := randNat rng1 2 15
    let (stack, rng3) := randomValueStack (x + 1) rng2
    (mkCaseCode s!"fuzz/raw-decoded-valid/x{x}-y15" stack (xchgCode 1 x), rng3)
  else if shape = 7 then
    let (x, rng2) := randNat rng1 1 15
    let (y, rng3) := randNat rng2 0 (x - 1)
    let (stack, rng4) := randomValueStack (x + 1) rng3
    (mkCaseCode s!"fuzz/raw-runtime-valid/x{x}-y{y}" stack (xchgCode x y), rng4)
  else
    let (x, rng2) := randNat rng1 1 14
    let (delta, rng3) := randNat rng2 1 (15 - x)
    let y : Nat := x + delta
    let (stack, rng4) := randomValueStack (y + 2) rng3
    (mkCase s!"fuzz/mixed-values/x{x}-y{y}" stack (#[.xchg x y]), rng4)


def suite : InstrSuite where
  id := xchgIjId
  unit := #[]
  oracle := #[
    -- [B1]
    mkCase "ok/swap-minimal-adjacent" #[intV 10, intV 20, intV 30] #[.xchg 1 2],
    -- [B1]
    mkCase "ok/swap-adjacent-with-nulls" #[.null, .cell Cell.empty, intV 77] #[.xchg 1 2],
    -- [B1]
    mkCase "ok/swap-mid-to-high" #[intV 1, intV 2, intV 3, intV 4] #[.xchg 2 3],
    -- [B1]
    mkCase "ok/swap-high-boundary" (stack16Base) #[.xchg 14 15],
    -- [B1]
    mkCase "ok/swap-edge-low-high" (stack16Base) #[.xchg 1 15],
    -- [B1]
    mkCase "ok/swap-full-depth-plus-noise" #[intV 0, intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10, intV 11, intV 12, intV 13, intV 14, intV 15, intV 16] #[.xchg 7 15],
    -- [B1]
    mkCase "ok/swap-with-boundary-values" #[intV maxInt257, intV minInt257, intV (-1), intV 0] #[.xchg 1 2],
    -- [B1]
    mkCase "ok/swap-with-continuation" #[.cont (.quit 0), intV 9, intV 8] #[.xchg 1 2],

    -- [B2]
    mkCaseCode "err/raw-invopcode-x0-y1" #[intV 1, intV 2, intV 3] (xchgCode 0 1),
    -- [B2]
    mkCaseCode "err/raw-invopcode-x0-y0" #[intV 4, intV 5, intV 6] (xchgCode 0 0),
    -- [B3]
    mkCaseCode "err/raw-invopcode-x9-y4" (stack16Base) (xchgCode 9 4),
    -- [B3]
    mkCaseCode "err/raw-invopcode-x1-y0" #[intV 99, intV 98] (xchgCode 1 0),

    -- [B4]
    mkCase "err/underflow-empty-stack" #[] #[.xchg 1 2],
    -- [B4]
    mkCase "err/underflow-one-element" #[intV 1] #[.xchg 1 2],
    -- [B4]
    mkCase "err/underflow-two-elements" #[intV 1, intV 2] #[.xchg 1 2],
    -- [B4]
    mkCase "err/underflow-deep-boundary" (Array.replicate 15 (intV 1)) #[.xchg 14 15],
    -- [B4]
    mkCase "err/underflow-mixed-short" (Array.replicate 5 (intV 42)) #[.xchg 4 12],


    -- [B6]
    mkCaseCode "err/decode/truncated-8" (Array.replicate 1 (intV 7)) xchgTruncated8Code,
    -- [B6]
    mkCaseCode "err/decode/truncated-15" (Array.replicate 1 (intV 7)) xchgTruncated15Code,

    -- [B6]
    mkCaseCode "ok/raw-decode-valid-x1-y2" #[intV 10, intV 11, intV 12] (xchgCode 1 2),
    -- [B6]
    mkCaseCode "ok/raw-decode-valid-x14-y15" (stack16Base) (xchgCode 14 15),

    -- [B7]
    mkCase "ok/gas/exact" #[intV 1, intV 2, intV 3] #[.pushInt (.num xchgSetGasExact), .tonEnvOp .setGasLimit, .xchg 1 2],
    -- [B7]
    mkCase "err/gas/exact-minus-one" #[intV 1, intV 2, intV 3] #[.pushInt (.num xchgSetGasExactMinusOne), .tonEnvOp .setGasLimit, .xchg 1 2],

    -- [B1]
    mkCase "ok/raw-branch-coverage" #[intV 100, intV 200, intV 300, intV 400, intV 500] #[.xchg 1 4],
    -- [B1]
    mkCase "ok/nonint-raw-mix" #[.null, .cell Cell.empty, .tuple #[], intV 12, .cont (.quit 0), intV 13, intV 14, intV 15] (#[.xchg 2 7])
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr xchgIjId
      count := 500
      gen := genXchgIjFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.XCHG_IJ
