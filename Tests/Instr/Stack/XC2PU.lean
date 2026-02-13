import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.XC2PU

/-
INSTRUCTION: XC2PU

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [Runtime/Normal] Underflow gate: `need < st.stack.size` where
   `need := max(x, y, z, 1)`.
   - success when `stack.size >= max(x,y,z,1)+1`
   - failure throws `stkUnd` when below this threshold.
2. [Runtime/Success] Success path for all well-typed values:
   values are moved by `swap 1 x`, `swap 0 y`, then `push (fetch z)`.
   - result depends on relative positions of `x`, `y`, and `z`.
3. [Runtime] No type checks in `XC2PU`; any `Value` variant can flow through swaps/fetch.
4. [Runtime/Edge aliasing] Index alias classes (x/y/z equalities) change final
   permutation and pushed value:
   - x == y
   - x == z
   - y == z
   - x == y == z (folded alias)
5. [Runtime/Edge aliases] Boundary indices `x` / `y` / `z` in {0,1,15} hit
   swap/no-op and near-maximum depth behavior.
6. [Assembler encoding] `.xc2pu x y z` encodes to 24-bit fixed opcode `0x541`.
   - valid when all params are 0..15
   - invalid params (`>15`) must throw `.rangeChk`.
7. [Decoder behavior] Decode dispatch must match only exact 24-bit forms:
   - `0x541` prefix => `.xc2pu x y z`
   - neighboring `0x540` and `0x542` must decode as `.xchg3` and `.xcpuxc`.
   - truncated prefixes that do not have enough bits must reject via `.invOpcode`.
8. [Gas accounting] Base gas only in this instruction path:
   - fixed opcode dispatch path contributes `gas_per_instr + instr_bits`.
   - no variable per-argument penalty exists.
   - so `exact` success and `exact - 1` out-of-gas branches are the gas-relevant boundary pair.

TOTAL BRANCHES: 8

Branch coverage mapping for this suite:
- [B1] Runtime: underflow (`stkUnd`) path.
- [B2] Runtime: success path general (all valid values, no underflow).
- [B3] Runtime: swap/fetch behavior with distinct indices.
- [B4] Runtime: x == y alias case.
- [B5] Runtime: x == z alias case.
- [B6] Runtime: y == z alias case.
- [B7] Runtime: y == 0 / x == 1 boundary-index effects.
- [B8] Runtime: type-agnostic value flow (non-int values preserved and moved).
- [B9] Assembler: in-range parameters encode successfully.
- [B10] Assembler: out-of-range `x`.
- [B11] Assembler: out-of-range `y`.
- [B12] Assembler: out-of-range `z`.
- [B13] Decoder: exact 0x541xxx decode branch.
- [B14] Decoder: neighboring 0x540xxx branch (`XCHG3`) does not decode as XC2PU.
- [B15] Decoder: neighboring 0x542xxx branch (`XCPUXC`) does not decode as XC2PU.
- [B16] Decoder: 8-bit truncated prefix is invalid.
- [B17] Decoder: 15-bit truncated prefix is invalid.
- [B18] Gas: exact budget path succeeds.
- [B19] Gas: exact-1 budget path fails.

No variable gas penalty category: gas behavior here is base-only (exact/ minus-one only).
-/

private def xc2puId : InstrId := { name := "XC2PU" }

private def vCell : Value := .cell Cell.empty
private def vSlice : Value := .slice (Slice.ofCell Cell.empty)
private def vBuilder : Value := .builder Builder.empty

private def intStackLen (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    return out

private def mkCase
    (name : String)
    (stack : Array Value)
    (x y z : Nat)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xc2puId
    program := #[.xc2pu x y z]
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
    instr := xc2puId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xc2puId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def xc2puGasExact : Int := computeExactGasBudget (.xc2pu 0 0 0)
private def xc2puGasExactMinusOne : Int := computeExactGasBudgetMinusOne (.xc2pu 0 0 0)

private def rawXC2PUCode : Cell :=
  Cell.mkOrdinary (natToBits (0x541345) 24) #[]

private def rawXCHG3Code : Cell :=
  Cell.mkOrdinary (natToBits (0x5402ab) 24) #[]

private def rawXCPUXCCode : Cell :=
  Cell.mkOrdinary (natToBits (0x542010) 24) #[]

private def rawXC2PUTrunc8 : Cell :=
  Cell.mkOrdinary (natToBits 0x54 8) #[]

private def rawXC2PUTrunc15 : Cell :=
  Cell.mkOrdinary (natToBits (0x541345 >>> 1) 15) #[]

private def xc2puDispatchSentinel : Int := 50_067

private def runXc2puDirect
    (x y z : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackXc2pu (.xc2pu x y z) stack

private def runXc2puWithNext
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackXc2pu instr (VM.push (intV xc2puDispatchSentinel)) stack

private def expectAssembleRangeErr (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .error .rangeChk => pure ()
  | .error e => throw (IO.userError s!"{label}: expected rangeChk, got {e}")
  | .ok _ => throw (IO.userError s!"{label}: expected rangeChk, got successful assembly")

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr)
    (expectedBits : Nat := 24) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else if rest.bitsRemaining != 0 || rest.refsRemaining != 0 then
        throw
          (IO.userError
            s!"{label}: expected empty decode tail, got bits={rest.bitsRemaining}, refs={rest.refsRemaining}")
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
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, bits, _rest) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr instr} ({bits} bits)")

private def valuePool : Array Value :=
  #[
    intV 0,
    intV 1,
    intV (-1),
    intV 3,
    intV (-7),
    intV 77,
    .null,
    vCell,
    vSlice,
    vBuilder,
    .cont (.quit 0)
  ]

private def pickValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (valuePool.size - 1)
  (valuePool[idx]!, rng1)

private def genRandomStack (depth : Nat) (rng0 : StdGen) : Array Value × StdGen :=
  Id.run do
    let mut out : Array Value := #[]
    let mut rng := rng0
    for _ in [0:depth] do
      let (v, rng') := pickValue rng
      out := out.push v
      rng := rng'
    pure (out, rng)

private def genXc2puFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/underflow/empty" #[] 0 0 0, rng1)
    else if shape = 1 then
      (mkCase "fuzz/underflow/singleton" #[intV 7] 0 0 0, rng1)
    else if shape = 2 then
      let (x, rng2) := randNat rng1 0 15
      let (y, rng3) := randNat rng2 0 15
      let (z, rng4) := randNat rng3 0 15
      let need : Nat := Nat.max (Nat.max (Nat.max x y) z) 1
      let (stack, rng5) := genRandomStack need rng4
      (mkCase s!"fuzz/underflow/boundary-{x}-{y}-{z}" stack x y z, rng5)
    else if shape = 3 then
      let (x, rng2) := randNat rng1 0 15
      let (y, rng3) := randNat rng2 0 15
      let (z, rng4) := randNat rng3 0 15
      let need : Nat := Nat.max (Nat.max (Nat.max x y) z) 1
      let (stack, rng5) := genRandomStack (need + 1) rng4
      (mkCase s!"fuzz/success/min-depth/{x}-{y}-{z}" stack x y z, rng5)
    else if shape = 4 then
      let (stack, rng3) := genRandomStack 8 rng1
      (mkCase "fuzz/success/distinct" stack 3 1 2, rng3)
    else if shape = 5 then
      let (stack, rng3) := genRandomStack 10 rng1
      (mkCase "fuzz/success/x-eq-y" stack 6 6 3, rng3)
    else if shape = 6 then
      let (stack, rng3) := genRandomStack 10 rng1
      (mkCase "fuzz/success/x-eq-z" stack 7 4 7, rng3)
    else if shape = 7 then
      let (stack, rng3) := genRandomStack 10 rng1
      (mkCase "fuzz/success/y-eq-z" stack 4 9 9, rng3)
    else if shape = 8 then
      let (stack, rng3) := genRandomStack 8 rng1
      (mkCase "fuzz/success/y-zero" stack 8 0 3, rng3)
    else if shape = 9 then
      let (stack, rng3) := genRandomStack 7 rng1
      (mkCase "fuzz/success/x-one" stack 1 9 4, rng3)
    else if shape = 10 then
      let (stack, rng3) := genRandomStack 6 rng1
      (mkCase "fuzz/success/mixed-values" stack 5 9 2, rng3)
    else if shape = 11 then
      let (stack, rng3) := genRandomStack 4 rng1
      (mkCase "fuzz/asm-bad-x" stack 16 1 2, rng3)
    else if shape = 12 then
      let (stack, rng3) := genRandomStack 4 rng1
      (mkCase "fuzz/asm-bad-y" stack 1 16 2, rng3)
    else if shape = 13 then
      let (stack, rng3) := genRandomStack 4 rng1
      (mkCase "fuzz/asm-bad-z" stack 1 2 16, rng3)
    else if shape = 14 then
      let (stack, rng2) := genRandomStack 4 rng1
      (mkCaseWithProgram ("fuzz/gas/exact" ++ s!"/{xc2puGasExact}")
        stack
        #[.pushInt (.num xc2puGasExact), .tonEnvOp .setGasLimit, .xc2pu 3 2 0]
        {} , rng2)
    else if shape = 15 then
      let (stack, rng2) := genRandomStack 4 rng1
      (mkCaseWithProgram ("fuzz/gas/exact-minus-one" ++ s!"/{xc2puGasExactMinusOne}")
        stack
        #[.pushInt (.num xc2puGasExactMinusOne), .tonEnvOp .setGasLimit, .xc2pu 3 2 0]
        {}, rng2)
    else if shape = 16 then
      (mkCaseCode "fuzz/decode/truncated-8" #[] rawXC2PUTrunc8, rng1)
    else
      (mkCaseCode "fuzz/decode/truncated-15" #[] rawXC2PUTrunc15, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)


def suite : InstrSuite where
  id := xc2puId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "unit/dispatch/fallback"
          (runXc2puWithNext .add #[intV 11, intV 22])
          #[intV 11, intV 22, intV xc2puDispatchSentinel] },
    { name := "unit/runtime/matched-basic"
      run := do
        expectOkStack "unit/runtime/matched-basic"
          (runXc2puDirect 1 0 1 #[intV 11, intV 22])
          #[intV 11, intV 22, intV 11] },
    { name := "unit/runtime/underflow-empty"
      run := do
        expectErr "unit/runtime/underflow-empty"
          (runXc2puDirect 0 0 0 #[])
          .stkUnd },
    { name := "unit/asm/range"
      run := do
        expectAssembleRangeErr "unit/asm/range-x" (.xc2pu 16 0 0)
        expectAssembleRangeErr "unit/asm/range-y" (.xc2pu 0 16 0)
        expectAssembleRangeErr "unit/asm/range-z" (.xc2pu 0 0 16) },
    { name := "unit/decode/raw"
      run := do
        expectDecodeOk "unit/decode/raw-541345" rawXC2PUCode (.xc2pu 3 4 5) },
    { name := "unit/decode/neighbors"
      run := do
        expectDecodeOk "unit/decode/neighbor-xchg3" rawXCHG3Code (.xchg3 2 10 11)
        expectDecodeOk "unit/decode/neighbor-xcpuxc" rawXCPUXCCode (.xcpuxc 0 1 0) },
    { name := "unit/decode/truncation"
      run := do
        expectDecodeErr "unit/decode/truncated-8" rawXC2PUTrunc8 .invOpcode
        match decodeCp0WithBits (Slice.ofCell rawXC2PUTrunc15) with
        | .ok (.xchg1 3, 8, _) => pure ()
        | .ok (instr, bits, _) =>
            throw
              (IO.userError
                s!"unit/decode/truncated-15: expected alias xchg1 3 (8), got {reprStr instr} ({bits} bits)")
        | .error e =>
            throw (IO.userError s!"unit/decode/truncated-15: expected alias xchg1 3 (8), got error {e}") }
  ]
  oracle := #[
    -- [B2, B9, B13]
    mkCase "ok/min-depth-boundary-1" #[intV 100, intV 200] 0 0 0
    -- [B1]
    , mkCase "err/underflow/empty" #[] 0 0 0
    -- [B1]
    , mkCase "err/underflow/singleton" #[intV 9] 0 0 0
    -- [B1]
    , mkCase "err/underflow/arg2-stack2" #[intV 10, intV 20] 2 5 2
    -- [B1]
    , mkCase "err/underflow/max-args" (intStackLen 15) 15 14 13
    -- [B2, B3, B13]
    , mkCase "ok/min-depth/max-args" (intStackLen 16) 15 14 13
    -- [B2, B3, B13]
    , mkCase "ok/depth-3-distinct" (intStackLen 4) 3 1 2
    -- [B2, B3]
    , mkCase "ok/distinct-deep" (intStackLen 8) 7 3 1
    -- [B4, B2]
    , mkCase "ok/x-eq-y" #[intV 11, intV 22, intV 33, intV 44, intV 55, intV 66] 6 6 2
    -- [B4, B8]
    , mkCase "ok/x-eq-y-non-int" #[.null, vCell, vSlice, vBuilder, intV 7] 4 4 0
    -- [B5, B2]
    , mkCase "ok/x-eq-z" #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6] 8 2 8
    -- [B5, B8]
    , mkCase "ok/x-eq-z-non-int" #[intV 0, .null, intV 9, vBuilder, vCell, intV 1] 2 1 2
    -- [B6, B2]
    , mkCase "ok/y-eq-z" #[intV 17, intV 18, intV 19, intV 20, intV 21, intV 22] 1 3 3
    -- [B6, B8]
    , mkCase "ok/y-eq-z-non-int" #[.cont (.quit 0), .null, intV 101, vSlice, intV 102] 3 2 2
    -- [B7, B2]
    , mkCase "ok/y-zero" #[intV 1, intV 2, intV 3, intV 4] 8 0 2
    -- [B7, B8]
    , mkCase "ok/y-zero-non-int" #[intV 9, vCell, .null, intV 42, vBuilder] 5 0 3
    -- [B7, B2]
    , mkCase "ok/x-one" #[intV 7, intV 8, intV 9, intV 10] 1 5 4
    -- [B7, B2]
    , mkCase "ok/x-one-mixed" #[.null, intV 7, vSlice, vBuilder, intV 11] 1 13 4
    -- [B8]
    , mkCase "ok/value-mix-non-int" #[.null, vCell, vSlice, vBuilder, .cont (.quit 0)] 2 4 1
    -- [B8]
    , mkCase "ok/all-equal-boundary" #[intV 555, intV 666, intV 777, intV 888] 15 15 15
    -- [B2, B3, B10]
    , mkCase "ok/with-boundary-ints" #[intV maxInt257, intV (-1), intV (maxInt257 - 1), intV minInt257, intV 0] 14 1 7
    -- [B8]
    , mkCase "ok/big-depth-with-null-cell-slice" #[intV 0, .null, vCell, vSlice, vBuilder, .cont (.quit 0), intV 42] 10 7 8
    -- [B13]
    , mkCaseCode "ok/decode/xc2pu-raw" (intStackLen 8) rawXC2PUCode
    -- [B14]
    , mkCaseCode "ok/decode/neighbor-0x540-xchg3" (intStackLen 3) rawXCHG3Code
    -- [B15]
    , mkCaseCode "ok/decode/neighbor-0x542-xcpuxc" (#[intV 4, intV 5]) rawXCPUXCCode
    -- [B16]
    , mkCaseCode "err/decode/truncated-8" #[] rawXC2PUTrunc8
    -- [B17]
    , mkCaseCode "err/decode/truncated-15" #[] rawXC2PUTrunc15
    -- [B18]
    , mkCaseWithProgram "gas/exact" (intStackLen 4) #[.pushInt (.num xc2puGasExact), .tonEnvOp .setGasLimit, .xc2pu 0 0 0]
      (oracleGasLimitsExact xc2puGasExact)
    -- [B19]
    , mkCaseWithProgram "gas/exact-minus-one" (intStackLen 4) #[.pushInt (.num xc2puGasExactMinusOne), .tonEnvOp .setGasLimit, .xc2pu 0 0 0]
      (oracleGasLimitsExactMinusOne xc2puGasExact)
    ]
  fuzz := #[
    { seed := 2026021301
      count := 500
      gen := genXc2puFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.XC2PU
