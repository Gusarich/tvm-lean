import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.PUSH_LONG

/-
INSTRUCTION: PUSH_LONG

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime success branch — short form `PUSH` index 0 (`0x20`) duplicates top stack value.
2. [B2] Runtime success branch — short form `PUSH` index 1 (`0x21`) duplicates stack item one below top.
3. [B3] Runtime success branch — short form indices 2–15 (`0x22..0x2f`) duplicates stack item at an arbitrary short offset and preserves full stack order.
4. [B4] Runtime success branch — long form indices 16–255 (`0x56 <idx>`) duplicates values from extended index offsets.
5. [B5] Runtime success branch — long-form maximum index (`idx=255`) succeeds when stack depth is 256.
6. [B6] Runtime underflow branch — short-form index `x` with `x ≥ stack.size` throws `stkUnd`.
7. [B7] Runtime underflow branch — long-form index `x` with `x ≥ stack.size` throws `stkUnd`.

8. [B8] Assembler success branch — `encodeCp0` maps `.push idx` with `idx=0` to `0x20`.
9. [B9] Assembler success branch — `.push idx` with `idx=1` to `0x21`.
10. [B10] Assembler success branch — `.push idx` with `2 ≤ idx ≤ 15` maps to `0x20 + idx`.
11. [B11] Assembler success branch — `.push idx` with `16 ≤ idx ≤ 255` maps to `0x56 ++ idx` (1 extra byte).
12. [B11] Assembler boundary branch — `.push idx` with `idx>255` throws `.rangeChk`.

13. [B12] Decode branch — `0x20` is decoded as `.push 0`.
14. [B13] Decode branch — `0x21` is decoded as `.push 1`.
15. [B14] Decode branch — `0x22..0x2f` is decoded as `.push 2..15`.
16. [B15] Decode branch — `0x56 ++ idx` is decoded as `.push idx`.
17. [B16] Decode error branch — `0x56` with missing payload argument throws `.invOpcode`.
18. [B17] Decode aliasing branch — opcode boundary to adjacent stack ops (`0x2f` is `PUSH 15`, `0x30` is `POP 0`, `0x56` is not ambiguous with `0x57 POP 0..255` without payload).

19. [B18] Gas branch — short-form `.push` exact budget succeeds (fixed-cost plus encoded bits).
20. [B19] Gas branch — short-form `.push` exact-budget-minus-one fails with out-of-gas.
21. [B20] Gas branch — long-form `.push` exact budget succeeds.
22. [B21] Gas branch — long-form `.push` exact-budget-minus-one fails with out-of-gas.

TOTAL BRANCHES: 22

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
Gas is base-cost + encoded-bitlength in both short and long forms; no other runtime penalty branches exist.
-/

private def pushLongId : InstrId :=
  { name := "PUSH_LONG" }

private def mkIntStack (n : Nat) (start : Int := 1) : Array Value :=
  Array.ofFn (n := n) (fun i : Fin n => intV (start + Int.ofNat i.1))

private def pushShort0Code : Cell :=
  Cell.mkOrdinary (natToBits 0x20 8) #[]

private def pushShort1Code : Cell :=
  Cell.mkOrdinary (natToBits 0x21 8) #[]

private def pushShort15Code : Cell :=
  Cell.mkOrdinary (natToBits 0x2f 8) #[]

private def pushLongCode (idx : Nat) : Cell :=
  Cell.mkOrdinary ((natToBits 0x56 8) ++ (natToBits idx 8)) #[]

private def pushLong56Truncated : Cell :=
  Cell.mkOrdinary (natToBits 0x56 8) #[]

private def pushLongAliasPopCode : Cell :=
  Cell.mkOrdinary (natToBits 0x30 8) #[]

private def stack16 : Array Value :=
  mkIntStack 16

private def stack17 : Array Value :=
  mkIntStack 17

private def stack255Plus : Array Value :=
  mkIntStack 256

private def stackMixed : Array Value :=
  #[intV 42, .null, intV (-7), .cell Cell.empty, .cont (.quit 0), intV 101, intV 202]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.push 0])
    (fuel : Nat := 1_000_000)
    (gasLimits : OracleGasLimits := {})
    : OracleCase :=
  { name := name
    instr := pushLongId
    program := program
    initStack := stack
    fuel := fuel
    gasLimits := gasLimits }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000)
    (gasLimits : OracleGasLimits := {})
    : OracleCase :=
  { name := name
    instr := pushLongId
    codeCell? := some code
    initStack := stack
    fuel := fuel
    gasLimits := gasLimits }

private def pushShortGasExact : Int :=
  computeExactGasBudget (.push 1)

private def pushShortGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.push 1)

private def pushLongGasExact : Int :=
  computeExactGasBudget (.push 255)

private def pushLongGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.push 255)

private def pickFuzzValue (rng : StdGen) : Value × StdGen :=
  let (k, rng') := randNat rng 0 6
  match k with
  | 0 => (intV 0, rng')
  | 1 => (intV 1, rng')
  | 2 => (intV (-1), rng')
  | 3 => (intV maxInt257, rng')
  | 4 => (intV minInt257, rng')
  | 5 => (.null, rng')
  | _ => (.cell Cell.empty, rng')

private def randomStack (n : Nat) (rng0 : StdGen) : Array Value × StdGen :=
  Id.run do
    let mut out : Array Value := #[]
    let mut rng := rng0
    for _ in List.range n do
      let (v, rng') := pickFuzzValue rng
      out := out.push v
      rng := rng'
    return (out, rng)

private def genPushLongFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  if shape = 0 then
    let (idx, rng2) := randNat rng1 0 15
    let (stack, rng3) := randomStack (idx + 2) rng2
    (mkCase s!"fuzz/ok/short/{idx}" stack #[.push idx], rng3)
  else if shape = 1 then
    let (idx, rng2) := randNat rng1 15 15
    (mkCase "fuzz/ok/short-boundary-15" stack17 #[.push idx], rng2)
  else if shape = 2 then
    let (idx, rng2) := randNat rng1 16 20
    let (stack, rng3) := randomStack (idx + 2) rng2
    (mkCase s!"fuzz/ok/long/{idx}" stack #[.push idx], rng3)
  else if shape = 3 then
    (mkCase "fuzz/ok/long-255-boundary" stack255Plus #[.push 255], rng1)
  else if shape = 4 then
    let (idx, rng2) := randNat rng1 0 15
    let (stack, rng3) := randomStack idx rng2
    (mkCase s!"fuzz/err/short-underflow/{idx}" stack #[.push idx], rng3)
  else if shape = 5 then
    (mkCase "fuzz/err/long-underflow-16" (mkIntStack 8) #[.push 16], rng1)
  else if shape = 6 then
    (mkCase "fuzz/err/long-underflow-255" (mkIntStack 16) #[.push 255], rng1)
  else if shape = 7 then
    (mkCase "fuzz/err/asm-range/256" (#[] ) #[.push 256], rng1)
  else if shape = 8 then
    let (idx, rng2) := randNat rng1 0 5
    let idx' : Nat := if idx = 0 then 0 else if idx = 1 then 1 else if idx = 2 then 2 else if idx = 3 then 15 else if idx = 4 then 16 else 255
    let (stack, rng3) := randomStack (idx' + 2) rng2
    (mkCaseCode s!"fuzz/decode/ok/{idx'}" stack (if idx' = 255 then pushLongCode 255 else if idx' = 16 then pushLongCode 16 else if idx' = 15 then pushShort15Code else if idx' = 2 then Cell.mkOrdinary (natToBits 0x22 8) #[] else if idx' = 1 then pushShort1Code else pushShort0Code), rng3)
  else if shape = 9 then
    let (idx, rng2) := randNat rng1 0 5
    let code : Cell :=
      if idx < 3 then
        pushLong56Truncated
      else if idx < 5 then
        pushLongCode (16 + idx)
      else
        pushLongCode 128
    (mkCaseCode s!"fuzz/decode/{idx}" (mkIntStack (idx + 20)) code, rng2)
  else if shape = 10 then
    (mkCaseCode "fuzz/decode/truncated-56" (#[]) pushLong56Truncated, rng1)
  else if shape = 11 then
    (mkCaseCode "fuzz/decode/alias-pop-30" stackMixed pushLongAliasPopCode, rng1)
  else if shape = 12 then
    (mkCase "fuzz/gas/exact-short" (mkIntStack 2) #[.pushInt (.num pushShortGasExact), .tonEnvOp .setGasLimit, .push 1], rng1)
  else if shape = 13 then
    (mkCase "fuzz/gas/exact-minus-one-short" (mkIntStack 2) #[.pushInt (.num pushShortGasExactMinusOne), .tonEnvOp .setGasLimit, .push 1], rng1)
  else if shape = 14 then
    (mkCase "fuzz/gas/exact-long" stack255Plus #[.pushInt (.num pushLongGasExact), .tonEnvOp .setGasLimit, .push 255], rng1)
  else if shape = 15 then
    (mkCase "fuzz/gas/exact-minus-one-long" stack255Plus #[.pushInt (.num pushLongGasExactMinusOne), .tonEnvOp .setGasLimit, .push 255], rng1)
  else
    let (idx, rng2) := randNat rng1 0 1
    let (_stack, rng3) := randomStack 64 rng2
    (if idx = 0 then
      mkCaseCode "fuzz/decode/mixed-short" stackMixed pushShort15Code
    else
      mkCase "fuzz/mixed-stack/multi-form" stackMixed (if idx = 1 then #[.push 15, .push 16] else #[.push 1]),
    rng3)

def suite : InstrSuite where
  id := pushLongId
  unit := #[]
  oracle := #[
    -- [B1]
    mkCase "ok/push0/top-duplicate" (mkIntStack 2) #[.push 0],
    -- [B2]
    mkCase "ok/push1/one-below-top" (mkIntStack 3) #[.push 1],
    -- [B3]
    mkCase "ok/push2/mixed-types" stackMixed #[.push 2],
    -- [B3]
    mkCase "ok/push15/bottom-boundary" stack16 #[.push 15],
    -- [B4]
    mkCase "ok/push16/long-start" stack17 #[.push 16],
    -- [B5]
    mkCase "ok/push255/max-long-boundary" stack255Plus #[.push 255],

    -- [B6]
    mkCase "err/push-underflow-empty" #[] #[.push 0],
    -- [B6]
    mkCase "err/push-underflow-short" (mkIntStack 1) #[.push 1],
    -- [B6]
    mkCase "err/push-underflow-short-boundary" (mkIntStack 15) #[.push 15],
    -- [B7]
    mkCase "err/push-underflow-long-boundary-16" (mkIntStack 8) #[.push 16],
    -- [B7]
    mkCase "err/push-underflow-long-255" (mkIntStack 16) #[.push 255],

    -- [B8]
    mkCase "ok/asm/push0" (mkIntStack 1) #[.push 0],
    -- [B9]
    mkCase "ok/asm/push1" (mkIntStack 2) #[.push 1],
    -- [B10]
    mkCase "ok/asm/push15" stack16 #[.push 15],
    -- [B11]
    mkCase "ok/asm/push16" stack17 #[.push 16],
    -- [B11]
    mkCase "ok/asm/push255" stack255Plus #[.push 255],

    -- [B12]
    mkCaseCode "ok/decode/push0" (mkIntStack 2) pushShort0Code,
    -- [B13]
    mkCaseCode "ok/decode/push1" (mkIntStack 2) pushShort1Code,
    -- [B14]
    mkCaseCode "ok/decode/push15" stack16 pushShort15Code,
    -- [B15]
    mkCaseCode "ok/decode/long16" stack17 (pushLongCode 16),
    -- [B15]
    mkCaseCode "ok/decode/long255" stack255Plus (pushLongCode 255),
    -- [B16]
    mkCaseCode "err/decode/truncated-56" (mkIntStack 1) pushLong56Truncated,
    -- [B17]
    mkCaseCode "ok/decode/alias-pop30" (mkIntStack 3) pushLongAliasPopCode,
    -- [B15]
    mkCaseCode "ok/decode/long-mixed" stackMixed (pushLongCode 42),
    -- [B10]
    mkCaseCode "ok/decode/short2" stackMixed (Cell.mkOrdinary (natToBits 0x22 8) #[]),

    -- [B18]
    mkCase "ok/gas/exact-short" (mkIntStack 2) #[.pushInt (.num pushShortGasExact), .tonEnvOp .setGasLimit, .push 1],
    -- [B19]
    mkCase "err/gas/exact-minus-one-short" (mkIntStack 2) #[.pushInt (.num pushShortGasExactMinusOne), .tonEnvOp .setGasLimit, .push 1],
    -- [B20]
    mkCase "ok/gas/exact-long" stack255Plus #[.pushInt (.num pushLongGasExact), .tonEnvOp .setGasLimit, .push 255],
    -- [B21]
    mkCase "err/gas/exact-minus-one-long" stack255Plus #[.pushInt (.num pushLongGasExactMinusOne), .tonEnvOp .setGasLimit, .push 255],

    -- [B10]
    mkCase "ok/asm/short1-mixed-stack" stackMixed #[.push 1],
    -- [B11]
    mkCase "ok/asm/long20-mixed-stack" (stackMixed ++ mkIntStack 30) #[.push 20]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr pushLongId
      count := 500
      gen := genPushLongFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.PUSH_LONG
