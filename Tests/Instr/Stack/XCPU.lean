import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.XCPU

/-\n+INSTRUCTION: XCPU

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime success:
   - Lean executes `need := max x y` and requires `need < stack.size`.
   - C++ executes `check_underflow_p(x, y)` which means `stack.depth() > x` and `> y`.
   - On success, Lean/CCPP both:
     - swap top (`0`) with index `x`,
     - fetch value at index `y`,
     - push that value onto the top.
2. [B2] Runtime underflow:
   - If either required index is out of range (`need >= size`), both Lean and C++ throw `.stkUnd`.
3. [B3] Runtime index-shape edge behavior:
   - Distinct outcomes for `x = 0`, `y = 0`, and `x = y` are all semantic branches inside the success path due index aliasing.
4. [B4] Assembler valid-encoding branch:
   - `.xcpu x y` is valid for any `x, y ∈ [0, 15]`,
   - encoded as fixed 16-bit `0x51xy`.
5. [B5] Assembler failure branch:
   - Any `x > 15` or `y > 15` must fail in assembler validation with `.rangeChk`.
6. [B6] Decoder success branch:
   - Byte `0x51` plus 8-bit args decodes to `.xcpu x y` from `x := args >>> 4`, `y := args &&& 0xf`.
7. [B7] Decoder adjacency branch:
   - `0x50` must decode as `XCHG2`, `0x52` must decode as `PUXC`; `0x51` must never alias.
8. [B8] Decoder truncation branch:
   - 8-bit/incomplete streams beginning with `0x51` must fail as `.invOpcode`.
9. [B9] Gas success threshold:
   - Fixed gas for instruction is `instrGas = Nat.max x y + 1` (from `Validation/Oracle/Runner.lean`).
10. [B10] Gas out-of-gas threshold:
    - `computeExactGasBudget` succeeds at exact budget and fails at exact-1 budget.
11. [B11] Gas-penalty branch:
    - no variable gas penalty was found for XCPU; gas path is fixed to `Nat.max x y + 1`.

TOTAL BRANCHES: 11
-/

private def xcpuId : InstrId := { name := "XCPU" }

private def makeIntStack (n : Nat) : Array Value := Id.run do
  let mut out : Array Value := #[]
  for i in [0:n] do
    out := out.push (intV (Int.ofNat i))
  return out

private def mkCase
    (name : String)
    (x y : Nat)
    (stack : Array Value)
    (program : Array Instr := #[.xcpu x y])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xcpuId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (code : Cell)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xcpuId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runXcpuDirect (x y : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackXcpu (.xcpu x y) stack

private def expectAssembleRangeErr
    (label : String)
    (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected rangeChk failure, got successful assembly")
  | .error e =>
      if e = .rangeChk then
        pure ()
      else
        throw (IO.userError s!"{label}: expected .rangeChk, got {e}")

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat)
    (expectEmpty : Bool := true) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else if expectEmpty && s'.bitsRemaining + s'.refsRemaining ≠ 0 then
        throw (IO.userError s!"{label}: expected empty tail, got {reprStr s'}")
      else
        pure s'

private def xcpuCode (x y : Nat) : Nat := (0x51 <<< 8) + (x <<< 4) + y

private def mkXcpuCode (x y : Nat) : Cell :=
  Cell.mkOrdinary (natToBits (xcpuCode x y) 16) #[]

private def makeValuePool : Array Value :=
  #[
    intV 0,
    intV 1,
    intV (-1),
    intV 17,
    intV (-17),
    intV maxInt257,
    intV (maxInt257 - 1),
    intV minInt257,
    intV (minInt257 + 1),
    .null,
    .cell Cell.empty,
    .slice (Slice.ofCell (Cell.mkOrdinary (natToBits 0x5a 8) #[])),
    .tuple #[],
    .builder Builder.empty,
    .cont (.quit 0)
  ]

private def pickBoundary (rng0 : StdGen) : Nat × StdGen :=
  let (choice, rng1) := randNat rng0 0 9
  let v : Nat :=
    match choice with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 3
    | 4 => 4
    | 5 => 5
    | 6 => 7
    | 7 => 8
    | 8 => 14
    | _ => 15
  (v, rng1)

private def pickValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (makeValuePool.size - 1)
  (makeValuePool[idx]!, rng1)

private def genXcpuStack (n : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  let mut i : Nat := 0
  while i < n do
    let (v, rng') := pickValue rng
    out := out.push v
    rng := rng'
    i := i + 1
  return (out, rng)

private def xcpuGasExact : Int :=
  computeExactGasBudget (.xcpu 15 0)

private def xcpuGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.xcpu 15 0)

private def genXcpuFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 99
  if shape < 55 then
    let (x, rng2) := pickBoundary rng1
    let (y, rng3) := pickBoundary rng2
    let need : Nat := max x y
    let (pad, rng4) := randNat rng3 0 4
    let (stack, rng5) := genXcpuStack (need + pad + 1) rng4
    let (tag, rng6) := randNat rng5 0 999_999
    ({ name := s!"/fuzz/success/{tag}", instr := xcpuId, program := #[.xcpu x y], initStack := stack }, rng6)
  else if shape < 78 then
    let (x, rng2) := pickBoundary rng1
    let (y, rng3) := pickBoundary rng2
    let need : Nat := max x y
    let (size, rng4) :=
      if need = 0 then
        (0, rng3)
      else
        randNat rng3 0 (need - 1)
    let (stack, rng5) := genXcpuStack size rng4
    let (tag, rng6) := randNat rng5 0 999_999
    ({ name := s!"/fuzz/underflow/{tag}", instr := xcpuId, program := #[.xcpu x y], initStack := stack }, rng6)
  else if shape < 88 then
    let (depth, rng2) := randNat rng1 0 14
    let (x, rng3) := randNat rng2 0 depth
    let y : Nat := if depth < 15 then depth + 1 else 15
    let (stack, rng4) := genXcpuStack depth rng3
    let (tag, rng5) := randNat rng4 0 999_999
    ({ name := s!"/fuzz/underflow-y/{tag}", instr := xcpuId, program := #[.xcpu x y], initStack := stack }, rng5)
  else if shape < 94 then
    let (tag, rng2) := randNat rng1 0 999_999
    ({ name := s!"/fuzz/decode/truncated8/{tag}", instr := xcpuId, codeCell? := some (Cell.mkOrdinary (natToBits 0x51 8) #[]), initStack := #[] }, rng2)
  else
    let (tag, rng2) := randNat rng1 0 999_999
    ({ name := s!"/fuzz/decode/raw/{tag}", instr := xcpuId, codeCell? := some (mkXcpuCode 0 0), initStack := makeIntStack 1 }, rng2)

def suite : InstrSuite where
  id := xcpuId
  unit := #[
    { name := "unit/dispatch/fallback-next"
      run := do
        expectOkStack "dispatch-fallback"
          (runHandlerDirectWithNext execInstrStackXcpu .add (VM.push (intV 7)) #[])
          #[intV 7]
    }
    ,
    { name := "unit/dispatch/matched-xcpu"
      run := do
        expectOkStack "dispatch-matched"
          (runXcpuDirect 0 1 #[intV 11, intV 22])
          #[intV 22, intV 11, intV 22]
    }
    ,
    { name := "unit/runtime/underflow-empty"
      run := do
        expectErr "underflow-empty" (runXcpuDirect 0 0 #[]) .stkUnd
    }
    ,
    { name := "unit/asm/valid-boundaries"
      run := do
        match assembleCp0 [(.xcpu 0 0), (.xcpu 15 15)] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"unit/asm/valid-boundaries: expected success, got {e}")
    }
    ,
    { name := "unit/asm/out-of-range"
      run := do
        expectAssembleRangeErr "asm/x-overflow" (.xcpu 16 0)
        expectAssembleRangeErr "asm/y-overflow" (.xcpu 0 16)
    }
    ,
    { name := "unit/decode/roundtrip"
      run := do
        let code ←
          match assembleCp0 [(.xchg2 2 3), (.xcpu 4 5), (.puxc 6 7)] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"unit/decode/roundtrip: expected assemble success, got {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/xchg2" s0 (.xchg2 2 3) 16
        let s2 ← expectDecodeStep "decode/xcpu" s1 (.xcpu 4 5) 16
        let _ ← expectDecodeStep "decode/puxc" s2 (.puxc 6 7) 16
        pure ()
    }
    ,
    { name := "unit/decode/truncated-fails"
      run := do
        let shortCode : Cell := Cell.mkOrdinary (natToBits 0x51 8) #[]
        match decodeCp0WithBits (Slice.ofCell shortCode) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/truncated-fails: expected invOpcode, got {e}")
        | .ok (instr, bits, _) => throw (IO.userError s!"decode/truncated-fails: expected failure, got {reprStr instr} ({bits} bits)")
    }
  ]
  oracle := #[
    -- [B1,B4]
    mkCase "ok/size1-x0-y0" 0 0 (makeIntStack 1)
    -- [B1,B3]
    , mkCase "ok/size2-x0-y1" 0 1 (#[intV 10, intV 20])
    -- [B1,B3]
    , mkCase "ok/size2-x1-y0" 1 0 (#[intV 30, intV 40])
    -- [B1]
    , mkCase "ok/size3-x2-y0" 2 0 (#[intV 1, intV 2, intV 3])
    -- [B1,B3]
    , mkCase "ok/size3-x2-y2" 2 2 (#[intV 11, intV 22, intV 33])
    -- [B1]
    , mkCase "ok/size4-x3-y1" 3 1 (#[intV 4, intV 5, intV 6, intV 7])
    -- [B1]
    , mkCase "ok/size5-x4-y5" 4 5 (makeIntStack 6)
    -- [B1]
    , mkCase "ok/size5-x0-y4" 0 4 (makeIntStack 6)
    -- [B1]
    , mkCase "ok/size8-x7-y0" 7 0 (makeIntStack 8)
    -- [B1,B4]
    , mkCase "ok/size8-x7-y0-non-int" 7 0 (#[.null, intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, intV 7])
    -- [B1,B3]
    , mkCase "ok/size8-x6-y7" 6 7 (#[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6, .cell Cell.empty, intV 8])
    -- [B1,B4]
    , mkCase "ok/size10-x9-y10" 9 10 (makeIntStack 11)
    -- [B1,B3]
    , mkCase "ok/size11-x10-y3-mix"
      10 3
      ((#[] : Array Value)
        |>.push (intV 0)
        |>.push .null
        |>.push (.cell Cell.empty)
        |>.push (intV 3)
        |>.push (intV 4)
        |>.push (intV 5)
        |>.push (intV 6))
    -- [B1,B4]
    , mkCase "ok/size12-x11-y12" 11 12 (makeIntStack 12)
    -- [B1,B3]
    , mkCase "ok/size15-x14-y15" 14 15 (makeIntStack 16)
    -- [B1]
    , mkCase "ok/size16-x15-y0" 15 0 (makeIntStack 16)
    -- [B1,B3]
    , mkCase "ok/size16-x15-y15" 15 15 (makeIntStack 16)
    -- [B1,B3]
    , mkCase "ok/size16-x0-y15" 0 15 (makeIntStack 16)
    -- [B1]
    , mkCase "ok/size16-x8-y14" 8 14 ((makeIntStack 16).set! 7 (.tuple #[]) |>.set! 10 (.cont (.quit 0)))
    -- [B1,B4]
    , mkCase "ok/size3-x0-y2-non-int" 0 2 (#[intV 10, .null, .cell Cell.empty])
    -- [B2]
    , mkCase "err/underflow-empty" 0 0 #[]
    -- [B2]
    , mkCase "err/underflow-size1-x0-y1" 0 1 (makeIntStack 1)
    -- [B2]
    , mkCase "err/underflow-size1-x1-y0" 1 0 (makeIntStack 1)
    -- [B2]
    , mkCase "err/underflow-size2-x2-y0" 2 0 (makeIntStack 2)
    -- [B2]
    , mkCase "err/underflow-size2-x0-y2" 0 2 (makeIntStack 2)
    -- [B2]
    , mkCase "err/underflow-size3-x3-y1" 3 1 (makeIntStack 3)
    -- [B2]
    , mkCase "err/underflow-size2-x1-y2-non-int" 1 2 (#[intV 3, .cell Cell.empty])
    -- [B2]
    , mkCase "err/underflow-size10-x10-y3" 10 3 (makeIntStack 10)
    -- [B2]
    , mkCase "err/underflow-size15-x15-y0" 15 0 (makeIntStack 15)
    -- [B2]
    , mkCase "err/underflow-size15-x0-y15" 0 15 (makeIntStack 15)
    -- [B2,B3]
    , mkCase "err/underflow-size4-x4-y4" 4 4 (makeIntStack 4)
    -- [B2]
    , mkCase "err/underflow-size1-all-cells" 0 1 (#[] |>.push .null)
    -- [B9,B10]
    , mkCase "gas/exact-cost-succeeds"
      15 0
      (makeIntStack 16)
      #[.pushInt (.num xcpuGasExact), .tonEnvOp .setGasLimit, .xcpu 15 0]
      (oracleGasLimitsExact xcpuGasExact)
    -- [B10]
    , mkCase "gas/exact-minus-one-fails"
      15 0
      (makeIntStack 16)
      #[.pushInt (.num xcpuGasExactMinusOne), .tonEnvOp .setGasLimit, .xcpu 15 0]
      (oracleGasLimitsExactMinusOne xcpuGasExactMinusOne)
  ]
  fuzz := #[
    { seed := 2026022101
      count := 500
      gen := genXcpuFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.XCPU
