import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Stack.REVERSE

/-
INSTRUCTION: REVERSE

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [Runtime/Normal] Normal success path requires `total := x + y <= st.stack.size`.
   - On success, the reversed segment is exactly `x` elements from index
     `start = stack.size - total` through `stop - 1`, where `stop = stack.size - y`.
2. [Runtime/Error] Underflow path when `total > st.stack.size` throws `.stkUnd`.
3. [Runtime/Edge] `y = 0` is a boundary case: reversal starts at `stack.size - x` and uses the stack top.
4. [Runtime/Edge] `.reverse 2 y` is minimal legal size; `.reverse 17 y` is maximal legal size.
5. [Runtime/Transform] `x` parity changes the internal swap count (`x / 2`) and middle-element behavior for odd `x`.
6. [Assembler/Normal] `.reverse x y` encodes to opcode `0x5e` with `args = ((x - 2) <<< 4) + y` and is valid only if `2 ≤ x ≤ 17` and `y ≤ 15`.
7. [Assembler/Error] Out-of-range encoding rejects:
   - `x < 2`
   - `x > 17`
   - `y > 15`
8. [Decoder] Raw byte `0x5e` plus 8-bit args decodes to `.reverse x y`, so round-trip encode→decode is identity on arguments.
9. [Decoder] Neighboring opcodes must remain distinct:
   - `0x5d` decodes to `.twoOver`
   - `0x5f00` decodes to `.blkdrop 0`
10. [Decoder] Truncated/partial streams must fail via decode error (`invOpcode` here through `decodeCp0WithBits`):
    - 8-bit prefix only.
    - 15-bit prefix only.
11. [Gas accounting] No data-dependent gas penalty exists beyond base fixed dispatch (`gas_per_instr + totBits`).
12. [Gas edge] Exact budget should pass; exact-minus-one should fail with OOG in oracle-run mode.

TOTAL BRANCHES: 12

Each oracle test below is tagged with [Bn] to the branch(es) it covers.
Category with zero branches: none.
-/

private def reverseId : InstrId := { name := "REVERSE" }

private def vCell : Value := .cell Cell.empty
private def vSlice : Value := .slice (Slice.ofCell Cell.empty)
private def vBuilder : Value := .builder Builder.empty
private def vCont : Value := .cont (.quit 0)

private def reverseCode (x y : Nat) : Cell :=
  let args : Nat := ((x - 2) <<< 4) + y
  Cell.mkOrdinary (natToBits (0x5e00 + args) 16) #[]

private def reverseRawTrunc8 : Cell :=
  Cell.mkOrdinary (natToBits 0x5e 8) #[]

private def reverseRawTrunc15 : Cell :=
  Cell.mkOrdinary (natToBits ((0x5e05 >>> 1)) 15) #[]

private def neighborTwoOverCode : Cell :=
  Cell.mkOrdinary (natToBits 0x5d 8) #[]

private def neighborBlkDropCode : Cell :=
  Cell.mkOrdinary (natToBits 0x5f00 16) #[]

private def reverseSetGasExact : Int :=
  computeExactGasBudget (.reverse 2 0)

private def reverseSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.reverse 2 0)

private def mkIntStack (n : Nat) : Array Value :=
  Id.run do
    let mut st : Array Value := #[]
    for i in [0:n] do
      st := st.push (intV (Int.ofNat (i + 1)))
    return st

private def mkCase
    (name : String)
    (stack : Array Value)
    (x y : Nat)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := reverseId
    program := #[.reverse x y]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseWithProgram
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := reverseId
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
    instr := reverseId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectAssembleOk (label : String) (x y : Nat) : IO Unit := do
  match assembleCp0 [.reverse x y] with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"{label}: expected assemble success, got {e}")

private def expectAssembleErr (label : String) (x y : Nat) : IO Unit := do
  match assembleCp0 [.reverse x y] with
  | .ok c => throw (IO.userError s!"{label}: expected rangeChk, got code {reprStr c}")
  | .error e =>
      if e != .rangeChk then
        throw (IO.userError s!"{label}: expected rangeChk, got {e}")

private def expectDecodeErr (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e != .invOpcode then
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode failure, got {reprStr instr} with {bits} bits")

private def valuePool : Array Value :=
  #[
    intV 0,
    intV 1,
    intV (-1),
    intV 7,
    intV (-7),
    intV maxInt257,
    intV minInt257,
    .null,
    vCell,
    vSlice,
    vBuilder,
    vCont
  ]

private def pickValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (valuePool.size - 1)
  (valuePool[idx]!, rng1)

private def randomStack (n : Nat) (rng0 : StdGen) : Array Value × StdGen :=
  Id.run do
    let mut out : Array Value := #[]
    let mut rng := rng0
    for _ in [0:n] do
      let (v, rng1) := pickValue rng
      out := out.push v
      rng := rng1
    return (out, rng)

private def genReverseFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/success/min-x2-y0" (mkIntStack 4) 2 0, rng1)
    else if shape = 1 then
      (mkCase "fuzz/success/min-x2-y15" (mkIntStack 20) 2 15, rng1)
    else if shape = 2 then
      (mkCase "fuzz/success/max-x17-y0" (mkIntStack 25) 17 0, rng1)
    else if shape = 3 then
      (mkCase "fuzz/success/max-x17-y15" (mkIntStack 40) 17 15, rng1)
    else if shape = 4 then
      let (x, rng2) := randNat rng1 2 17
      let (y, rng3) := randNat rng2 0 15
      let need : Nat := x + y
      let (extra, rng4) := randNat rng3 0 8
      let (stack, rng5) := randomStack (need + extra) rng4
      (mkCase s!"fuzz/success/random-x{x}-y{y}" stack x y, rng5)
    else if shape = 5 then
      (mkCase "fuzz/underflow/x2-y0-empty" #[] 2 0, rng1)
    else if shape = 6 then
      (mkCase "fuzz/underflow/x2-y1-empty" #[] 2 1, rng1)
    else if shape = 7 then
      let (x, rng2) := randNat rng1 2 17
      let (y, rng3) := randNat rng2 0 15
      let need : Nat := x + y
      let (shortage, rng4) := randNat rng3 0 (need - 1)
      let (stack, rng5) := randomStack shortage rng4
      (mkCase s!"fuzz/underflow/random-boundary-{x}-{y}" stack x y, rng5)
    else if shape = 8 then
      (mkCaseWithProgram "fuzz/asm/x-too-small" (mkIntStack 4) #[.reverse 1 0], rng1)
    else if shape = 9 then
      (mkCaseWithProgram "fuzz/asm/x-too-large" (mkIntStack 4) #[.reverse 18 0], rng1)
    else if shape = 10 then
      (mkCaseWithProgram "fuzz/asm/y-too-large" (mkIntStack 4) #[.reverse 2 16], rng1)
    else if shape = 11 then
      let (x, rng2) := randNat rng1 2 17
      let (y, rng3) := randNat rng2 0 15
      (mkCaseCode (s!"fuzz/decode/raw-x{x}-y{y}") (mkIntStack (x + y + 1)) (reverseCode x y), rng3)
    else if shape = 12 then
      (mkCaseCode "fuzz/decode/truncated-8" #[] reverseRawTrunc8, rng1)
    else if shape = 13 then
      (mkCaseCode "fuzz/decode/truncated-15" #[] reverseRawTrunc15, rng1)
    else if shape = 14 then
      (mkCaseWithProgram "fuzz/gas/exact" (mkIntStack 4) #[.pushInt (.num reverseSetGasExact), .tonEnvOp .setGasLimit, .reverse 5 2]
          (oracleGasLimitsExact reverseSetGasExact), rng1)
    else
      (mkCaseWithProgram "fuzz/gas/exact-minus-one" (mkIntStack 4) #[.pushInt (.num reverseSetGasExactMinusOne), .tonEnvOp .setGasLimit, .reverse 5 2]
          (oracleGasLimitsExactMinusOne reverseSetGasExact), rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)


def suite : InstrSuite where
  id := reverseId
  unit := #[
    { name := "unit/asm/ok/min-boundaries"
      run := do
        expectAssembleOk "unit/asm/min-2-0" 2 0
        expectAssembleOk "unit/asm/max-17-15" 17 15
        expectAssembleOk "unit/asm/boundary-10-9" 10 9 },
    { name := "unit/asm/err/out-of-range"
      run := do
        expectAssembleErr "unit/asm/x-too-small" 1 0
        expectAssembleErr "unit/asm/x-too-large" 18 0
        expectAssembleErr "unit/asm/y-too-large" 2 16 },
    { name := "unit/decode/valid-and-trunc"
      run := do
        let _ ← expectDecodeStep "unit/decode/valid/x4-y5" (reverseCode 4 5 |> Slice.ofCell)
          (.reverse 4 5) 16
        expectDecodeErr "unit/decode/truncated-8" reverseRawTrunc8
        expectDecodeErr "unit/decode/truncated-15" reverseRawTrunc15 }
  ]
  oracle := #[
    -- [B1, B3, B5]
    mkCase "ok/min-x2-y0" (mkIntStack 4) 2 0,
    -- [B1, B3]
    mkCase "ok/min-x2-y1" (mkIntStack 3) 2 1,
    -- [B1, B5]
    mkCase "ok/odd-x3-y0" (mkIntStack 6) 3 0,
    -- [B1, B5]
    mkCase "ok/odd-x3-y2" (mkIntStack 7) 3 2,
    -- [B1, B4]
    mkCase "ok/min-boundary-max-y" (mkIntStack 20) 2 15,
    -- [B1, B5, B4]
    mkCase "ok/max-x17-y0" (mkIntStack 25) 17 0,
    -- [B1, B5, B4]
    mkCase "ok/max-x17-y15" (mkIntStack 50) 17 15,
    -- [B1, B8]
    mkCase "ok/max-x10-y14-mix" (#[intV 0, .null, vCell, .slice (Slice.ofCell Cell.empty), intV 7, vBuilder, intV (-2), vCont, intV 123, intV 321]) 10 14,
    -- [B1]
    mkCase "ok/x7-y7" (mkIntStack 12) 7 7,
    -- [B1]
    mkCase "ok/x16-y1" (mkIntStack 20) 16 1,
    -- [B1, B2]
    mkCase "err/underflow/empty" #[] 2 0,
    -- [B2]
    mkCase "err/underflow/one" (mkIntStack 1) 2 0,
    -- [B2]
    mkCase "err/underflow/size-one-short" (#[intV 1, intV 2]) 2 3,
    -- [B2]
    mkCase "err/underflow/max-boundary" (mkIntStack 31) 17 15,
    -- [B2]
    mkCase "err/underflow/random-small" (mkIntStack 10) 12 10,
    -- [B5]
    mkCaseWithProgram "err/asm/x-too-small" (mkIntStack 4) #[.reverse 1 0],
    -- [B5]
    mkCaseWithProgram "err/asm/x-too-large" (mkIntStack 4) #[.reverse 18 0],
    -- [B5]
    mkCaseWithProgram "err/asm/y-too-large" (mkIntStack 4) #[.reverse 2 16],
    -- [B8]
    mkCaseCode "ok/decode/valid-x4-y9" (mkIntStack 13) (reverseCode 4 9),
    -- [B8]
    mkCaseCode "ok/decode/valid-x17-y15" (mkIntStack 40) (reverseCode 17 15),
    -- [B9]
    mkCaseCode "err/decode/neighbor-5d" (#[intV 1, intV 2]) neighborTwoOverCode,
    -- [B9]
    mkCaseCode "err/decode/neighbor-5f00" #[] neighborBlkDropCode,
    -- [B10]
    mkCaseCode "err/decode/truncated-8" #[] reverseRawTrunc8,
    -- [B10]
    mkCaseCode "err/decode/truncated-15" #[] reverseRawTrunc15,
    -- [B11, B12]
    mkCaseWithProgram "gas/exact" (mkIntStack 4)
      #[.pushInt (.num reverseSetGasExact), .tonEnvOp .setGasLimit, .reverse 2 0]
      (oracleGasLimitsExact reverseSetGasExact),
    -- [B11, B12]
    mkCaseWithProgram "gas/exact-minus-one" (mkIntStack 4)
      #[.pushInt (.num reverseSetGasExactMinusOne), .tonEnvOp .setGasLimit, .reverse 2 0]
      (oracleGasLimitsExactMinusOne reverseSetGasExact)
  ]
  fuzz := #[
    { seed := 2026021309
      count := 500
      gen := genReverseFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.REVERSE
