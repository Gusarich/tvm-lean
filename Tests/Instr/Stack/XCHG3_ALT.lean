import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.XCHG3_ALT

/-
INSTRUCTION: XCHG3_ALT

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Normal short-form execution (`.xchg3` decoded from short family):
  - Lean: `execInstrStackXchg3` computes `need := max(max(x, y, z), 2)` and requires `need < st.stack.size`, then executes `swap(2,x)`, `swap(1,y)`, `swap(0,z)`.
  - C++: `exec_xchg3` calls `stack.check_underflow_p(x, y, z, 2)`; for values as indices this is exactly the same size requirement.
  - Any values/types are acceptable for success as long as stack depth is sufficient; this includes distinct and duplicate indices.

2. [B2] Normal long-form execution (`0x540` decode family):
  - Lean `Codepage/Cp0.lean` accepts opcode family `0x540` and decodes to `.xchg3`.
  - C++ opcode table also registers `(0x540,12,12)` to the same C++ handler.
  - Runtime behavior is identical to B1 after decode.

3. [B3] Runtime underflow branch:
  - Both Lean and C++ fail with `stkUnd` when `need + 1 > stack.size`.
  - This includes both short- and long-form decoded instructions.

4. [B4] Assembler argument-range branch:
  - Lean assembler `Asm/Cp0` accepts only `0..15` for each `.xchg3` argument.
  - Any `16` (or larger) argument is rejected at assemble-time with `.rangeChk`.
  - There are no runtime `invOpcode` checks here for `xchg3` in C++; only runtime underflow applies.

5. [B5] Decoder short-form malformed prefix branch:
  - Short form is a 16-bit fixed opcode with 4-bit prefix (`0x4`) and 12-bit args.
  - 8-bit or 15-bit prefixes must fail with `invOpcode`.

6. [B6] Decoder long-form malformed/aliasing branch:
  - Long form is a 24-bit fixed opcode with 12-bit prefix (`0x540`).
  - `XC2PU` at `0x541` must remain a distinct decode target; this suite also covers adjacent opcode boundaries via raw-cells.
  - `24`-bit truncations fail in the same decoder mode.

7. [B7] Gas accounting:
  - Base gas only, no penalties: `gas_per_instr + tot_bits`.
  - short form: `26`, long form: `34`.
  - exact-gas-success and exact-gas-minus-one-failure are both covered.

TOTAL BRANCHES: 7

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
Gas has no variable penalty: only exact base-cost behavior is exercised.
-/

private def xchg3AltId : InstrId := { name := "XCHG3_ALT" }

private def xchg3Instr (x y z : Nat) : Instr := .xchg3 x y z

private def xchg3Need (x y z : Nat) : Nat := Nat.max 2 (Nat.max (Nat.max x y) z)

private def xchg3ShortWord (x y z : Nat) : Nat := 0x4000 + ((x <<< 8) + (y <<< 4) + z)

private def xchg3AltWord (x y z : Nat) : Nat := (0x540 <<< 12) + ((x <<< 8) + (y <<< 4) + z)

private def xchg3ShortCode (x y z : Nat) : Cell :=
  Cell.mkOrdinary (natToBits (xchg3ShortWord x y z) 16) #[]

private def xchg3AltCode (x y z : Nat) : Cell :=
  Cell.mkOrdinary (natToBits (xchg3AltWord x y z) 24) #[]

private def xchg3ShortTrunc8Code : Cell :=
  Cell.mkOrdinary (natToBits 0x40 8) #[]

private def xchg3ShortTrunc15Code : Cell :=
  Cell.mkOrdinary (natToBits ((xchg3ShortWord 5 6 7) >>> 1) 15) #[]

private def xchg3AltTrunc23Code : Cell :=
  Cell.mkOrdinary (natToBits ((xchg3AltWord 5 6 7) >>> 1) 23) #[]

private def xchg3AltTrunc15Code : Cell :=
  Cell.mkOrdinary (natToBits ((xchg3AltWord 3 2 1) >>> 9) 15) #[]

private def xchg3AltNeighborCode : Cell :=
  Cell.mkOrdinary (natToBits (0x541000 + 0) 24) #[]

private def xchg3AltGasExact : Int := 34

private def xchg3AltGasExactMinusOne : Int := 33

private def xchg3AltRawStepGasExact : Int :=
  xchg3AltGasExact + implicitRetGasPrice

private def gasCostWithFallback (instr : Instr) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok gas => gas
  | .error _ => instrGas instr 16

private def xchg3AltSetGasNeed (budget : Int) : Int :=
  gasCostWithFallback (.pushInt (.num budget))
    + gasCostWithFallback (.tonEnvOp .setGasLimit)
    + xchg3AltRawStepGasExact

private def xchg3AltSetGasExact : Int :=
  let rec loop (n : Int) (iters : Nat) : Int :=
    match iters with
    | 0 => n
    | k + 1 =>
        let n' := xchg3AltSetGasNeed n
        if n' = n then n else loop n' k
  loop 64 16

private def xchg3AltSetGasExactMinusOne : Int :=
  if xchg3AltSetGasExact > 0 then xchg3AltSetGasExact - 1 else 0

private def xchg3AltGasProgramCode (budget : Int) : Cell :=
  match encodeCp0 (.pushInt (.num budget)), encodeCp0 (.tonEnvOp .setGasLimit) with
  | .ok pushBits, .ok setGasBits =>
      Cell.mkOrdinary (pushBits ++ setGasBits ++ natToBits (xchg3AltWord 1 2 3) 24) #[]
  | _, _ =>
      Cell.mkOrdinary (natToBits (xchg3AltWord 1 2 3) 24) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[xchg3Instr 1 2 3])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xchg3AltId
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
    instr := xchg3AltId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def stack16 : Array Value :=
  #[
    intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8,
    intV 9, intV 10, intV 11, intV 12, intV 13, intV 14, intV 15, intV 16
  ]

private def pickXchg3Token (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 8
  if pick = 0 then
    (intV 0, rng')
  else if pick = 1 then
    (intV 1, rng')
  else if pick = 2 then
    (intV (-1), rng')
  else if pick = 3 then
    (intV maxInt257, rng')
  else if pick = 4 then
    (intV minInt257, rng')
  else if pick = 5 then
    (.null, rng')
  else if pick = 6 then
    (.cell Cell.empty, rng')
  else if pick = 7 then
    (.builder Builder.empty, rng')
  else
    (.tuple #[], rng')

private def randomXchg3Stack (size : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut stack : Array Value := #[]
  let mut rng := rng0
  for _ in [0:size] do
    let (v, rng') := pickXchg3Token rng
    stack := stack.push v
    rng := rng'
  return (stack, rng)

private def pickXchg3Args (rng0 : StdGen) : (Nat × Nat × Nat × StdGen) :=
  let (x, rng1) := randNat rng0 0 15
  let (y, rng2) := randNat rng1 0 15
  let (z, rng3) := randNat rng2 0 15
  (x, y, z, rng3)

private def pickDupXchg3Args (rng0 : StdGen) : (Nat × Nat × Nat × StdGen) :=
  let (x, rng1) := randNat rng0 0 15
  let (mode, rng2) := randNat rng1 0 2
  if mode = 0 then
    let (z, rng3) := randNat rng2 0 15
    (x, x, z, rng3)
  else if mode = 1 then
    let (y, rng3) := randNat rng2 0 15
    (x, y, y, rng3)
  else
    (x, x, x, rng2)

private def genXchg3AltFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  if shape = 0 then
    let (x, y, z, rng2) := pickXchg3Args rng1
    let need := xchg3Need x y z
    let (extra, rng3) := randNat rng2 0 4
    let (stack, rng4) := randomXchg3Stack (need + 1 + extra) rng3
    (mkCase s!"fuzz/ok/short/distinct/x{x}-y{y}-z{z}" stack (#[xchg3Instr x y z]), rng4)
  else if shape = 1 then
    let (x, y, z, rng2) := pickDupXchg3Args rng1
    let need := xchg3Need x y z
    let (extra, rng3) := randNat rng2 0 3
    let (stack, rng4) := randomXchg3Stack (need + 1 + extra) rng3
    (mkCase s!"fuzz/ok/short/duplicate/x{x}-y{y}-z{z}" stack (#[xchg3Instr x y z]), rng4)
  else if shape = 2 then
    let (x, y, z, rng2) := pickXchg3Args rng1
    let need := xchg3Need x y z
    let (depth, rng3) := randNat rng2 0 need
    let (stack, rng4) := randomXchg3Stack depth rng3
    (mkCase s!"fuzz/err/underflow/x{x}-y{y}-z{z}" stack (#[xchg3Instr x y z]), rng4)
  else if shape = 3 then
    let (x, y, z, rng2) := pickXchg3Args rng1
    let need := xchg3Need x y z
    let depth := need + 2
    let (stack, rng3) := randomXchg3Stack depth rng2
    (mkCaseCode s!"fuzz/raw/ok/short/x{x}-y{y}-z{z}" stack (xchg3ShortCode x y z), rng3)
  else if shape = 4 then
    let (x, y, z, rng2) := pickDupXchg3Args rng1
    let need := xchg3Need x y z
    let (extra, rng3) := randNat rng2 0 4
    let (stack, rng4) := randomXchg3Stack (need + 1 + extra) rng3
    (mkCaseCode s!"fuzz/raw/ok/alt/x{x}-y{y}-z{z}" stack (xchg3AltCode x y z), rng4)
  else if shape = 5 then
    let (x, y, z, rng2) := pickXchg3Args rng1
    let (depth, rng3) := randNat rng2 0 (Nat.max 2 (Nat.max x (Nat.max y z)))
    let (stack, rng4) := randomXchg3Stack depth rng3
    (mkCaseCode s!"fuzz/raw/err/alt-underflow/x{x}-y{y}-z{z}" stack (xchg3AltCode x y z), rng4)
  else if shape = 6 then
    let (stack, rng2) := randomXchg3Stack 3 rng1
    let (pick, rng3) := randNat rng2 0 2
    if pick = 0 then
      (mkCase "fuzz/err/asm/x-overflow" stack (#[xchg3Instr 16 1 2]), rng3)
    else if pick = 1 then
      (mkCase "fuzz/err/asm/y-overflow" stack (#[xchg3Instr 1 16 2]), rng3)
    else
      (mkCase "fuzz/err/asm/z-overflow" stack (#[xchg3Instr 1 2 16]), rng3)
  else if shape = 7 then
    (mkCase "fuzz/err/asm/all-overflow" #[] (#[xchg3Instr 16 16 16]), rng1)
  else if shape = 8 then
    let (pick, rng2) := randNat rng1 0 1
    let (stack, rng3) := randomXchg3Stack 1 rng2
    if pick = 0 then
      (mkCaseCode "fuzz/raw/err/short/trunc8" stack xchg3ShortTrunc8Code, rng3)
    else
      (mkCaseCode "fuzz/raw/err/short/trunc15" stack xchg3ShortTrunc15Code, rng3)
  else if shape = 9 then
    let (pick, rng2) := randNat rng1 0 1
    let (stack, rng3) := randomXchg3Stack 1 rng2
    if pick = 0 then
      (mkCaseCode "fuzz/raw/err/alt/trunc23" stack xchg3AltTrunc23Code, rng3)
    else
      (mkCaseCode "fuzz/raw/err/alt/trunc15" stack xchg3AltTrunc15Code, rng3)
  else if shape = 10 then
    let (pick, rng2) := randBool rng1
    if pick then
      (mkCaseCode "fuzz/raw/ok/neighbor/xc2pu" #[] xchg3AltNeighborCode, rng2)
    else
      (mkCaseCode "fuzz/raw/ok/alt/high-args" stack16 (xchg3AltCode 15 15 15), rng2)
  else if shape = 11 then
    let (stack, rng2) := randomXchg3Stack 4 rng1
    let (exact, rng4) := randBool rng2
    if exact then
      (mkCaseCode "fuzz/gas/exact/alt" stack (xchg3AltGasProgramCode xchg3AltSetGasExact), rng4)
    else
      (mkCaseCode "fuzz/gas/exact-minus-one/alt" stack (xchg3AltGasProgramCode xchg3AltSetGasExactMinusOne), rng4)
  else if shape = 12 then
    let (depth, rng2) := randNat rng1 0 6
    let (stack, rng3) := randomXchg3Stack depth rng2
    (mkCaseCode "fuzz/raw/ok/alt/min" stack (xchg3AltCode 0 0 0), rng3)
  else
    let (x, y, z, rng2) := pickXchg3Args rng1
    let need := xchg3Need x y z
    let (depth, rng3) := randNat rng2 0 need
    let (stack, rng4) := randomXchg3Stack depth rng3
    (mkCaseCode "fuzz/raw/err/alt-needs-more" stack (xchg3AltCode x y z), rng4)

def suite : InstrSuite where
  id := xchg3AltId
  unit := #[]
  oracle := #[
    -- [B1] short successful distinct-index paths
    mkCase "ok/short/distinct/minimal" #[intV 10, intV 20, intV 30] (#[.xchg3 0 1 2]),
    mkCase "ok/short/distinct/with-noise" #[
      .null, .cell Cell.empty, intV 42, intV 7, intV (-3), .builder Builder.empty, intV 0
    ] (#[.xchg3 2 4 1]),
    mkCase "ok/short/distinct/high-boundary" stack16 (#[.xchg3 14 15 12]),
    mkCase "ok/short/distinct/top-preserve" #[
      intV 101, intV (-1), .tuple #[], intV 202, .cont (.quit 0), intV 303
    ] (#[.xchg3 1 3 4]),
    mkCase "ok/short/distinct/max-depth" #[
      intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8,
      intV 9, intV 10, intV 11, intV 12, intV 13, intV 14, intV 15, intV 16, intV 17
    ] (#[.xchg3 12 15 9]),

    -- [B2] short duplicate-index behavior
    mkCase "ok/short/duplicate/x-eq-y" #[intV 1, intV 2, intV 3, intV 4, intV 5] (#[.xchg3 3 3 1]),
    mkCase "ok/short/duplicate/y-eq-z" #[intV 8, intV 9, intV 10, intV 11, intV 12] (#[.xchg3 4 2 2]),
    mkCase "ok/short/duplicate/all-eq" #[intV 7, intV 8, intV 9, intV 10] (#[.xchg3 0 0 0]),
    mkCase "ok/short/duplicate/nonint" #[
      .null, intV 1, .cell Cell.empty, .builder Builder.empty, intV 2, .tuple #[], intV 3
    ] (#[.xchg3 5 1 5]),

    -- [B3] underflow path
    mkCase "err/underflow/empty" #[] (#[.xchg3 1 2 3]),
    mkCase "err/underflow/one" #[intV 99] (#[.xchg3 0 1 2]),
    mkCase "err/underflow/two" #[intV 99, intV 100] (#[.xchg3 2 1 3]),
    mkCase "err/underflow/deep-at-boundary" (stack16.extract 0 15) (#[.xchg3 14 15 13]),
    mkCase "err/underflow/max-args" (stack16) (#[.xchg3 15 15 15]),


    -- [B5] short decoder boundaries and malformed prefixes
    mkCaseCode "ok/raw/short/valid-0-1-2" #[intV 1, intV 2, intV 3] (xchg3ShortCode 0 1 2),
    mkCaseCode "ok/raw/short/valid-15-15-15" stack16 (xchg3ShortCode 15 15 15),
    mkCaseCode "err/raw/short/truncated-8" #[intV 1] xchg3ShortTrunc8Code,
    mkCaseCode "err/raw/short/truncated-15" #[intV 2] xchg3ShortTrunc15Code,

    -- [B6] long/alt decoder boundaries and adjacency/alias checks
    mkCaseCode "ok/raw/alt/valid-0-1-2" #[intV 1, intV 2, intV 3] (xchg3AltCode 0 1 2),
    mkCaseCode "ok/raw/alt/valid-15-15-15" stack16 (xchg3AltCode 15 15 15),
    mkCaseCode "ok/raw/alt/duplicate/low" #[intV 1, intV 2, intV 3] (xchg3AltCode 0 0 0),
    mkCaseCode "err/raw/alt/truncated-23" #[intV 4] xchg3AltTrunc23Code,
    mkCaseCode "err/raw/alt/truncated-15" #[intV 5] xchg3AltTrunc15Code,
    mkCaseCode "ok/raw/adjacent-is-not-xchg3" #[intV 9, intV 8] xchg3AltNeighborCode,
    -- [B7] gas edge via embedded setGasLimit + raw alt opcode.
    mkCaseCode "ok/gas/exact" #[intV 1, intV 2, intV 3, intV 4]
      (xchg3AltGasProgramCode xchg3AltSetGasExact),
    mkCaseCode "err/gas/exact-minus-one" #[intV 1, intV 2, intV 3, intV 4]
      (xchg3AltGasProgramCode xchg3AltSetGasExactMinusOne),

  ]
  fuzz := #[
    { seed := fuzzSeedForInstr xchg3AltId
      count := 500
      gen := genXchg3AltFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.XCHG3_ALT
