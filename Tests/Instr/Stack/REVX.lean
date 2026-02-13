import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.REVX

/-!
INSTRUCTION: REVX

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch branch:
   - `execInstrStackReverseX` runs only on `.reverseX`; all other instructions go through `next`.
2. [B2] Runtime pre-pop underflow:
   - `y` is popped first and an empty stack triggers `.stkUnd`.
3. [B3] Runtime `y` type error:
   - non-Int `y` triggers `.typeChk` (e.g. `.null`, `.cell`, `.slice`).
4. [B4] Runtime `y` range error for negative Int.
5. [B5] Runtime `y` range error for NaN.
6. [B6] Runtime `y` range error for `y > (1 <<< 30) - 1`.
7. [B7] Runtime second-pop underflow:
   - `y` is valid but no `x` remains on stack.
8. [B8] Runtime `x` type error:
   - non-Int `x` triggers `.typeChk`.
9. [B9] Runtime `x` range error for negative Int.
10. [B10] Runtime `x` range error for NaN.
11. [B11] Runtime `x` range error for `x > (1 <<< 30) - 1`.
12. [B12] Runtime underflow after pops when `x + y > payload` depth.
13. [B13] Success no-op branch (`x = 0`) reverses an empty segment.
14. [B14] Success branch with `y = 0`:
   - reverses the top `x` elements.
15. [B15] Success branch with `x > 0` and `y > 0`:
   - reverses the `x` elements below `y` top elements.
16. [B16] Assembler encoding branch:
   - `.reverseX` has a fixed opcode (`0x64`) and no immediate operands.
17. [B17] Assembler argument branch:
   - no separate argument-range branch exists (zero-operand instruction).
18. [B18] Decoder exact path:
   - raw `0x64` decodes to `.reverseX` consuming exactly 8 bits.
19. [B19] Decoder adjacency path:
   - neighbors `0x63`/`0x65` decode to `.blkSwapX`/`.dropX`.
20. [B20] Decoder malformed/truncated path:
   - 7-bit stream must fail with `.invOpcode`.
21. [B21] Gas base path:
   - `x ≤ 255`: no variable penalty beyond `computeExactGasBudget`.
22. [B22] Gas penalty path:
   - `x > 255`: extra cost `x - 255`.
23. [B23] Gas edge path:
   - exact-gas succeeds and exact-minus-one fails.

TOTAL BRANCHES: 23

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by the fuzzer.
-/

private def revXId : InstrId := { name := "REVX" }
private def revXInstr : Instr := .reverseX
private def maxArg : Int := (1 <<< 30) - 1

private def revXCode : Cell := Cell.mkOrdinary (natToBits 0x64 8) #[]
private def revXNeighborBlkSwapX : Cell := Cell.mkOrdinary (natToBits 0x63 8) #[]
private def revXNeighborDropX : Cell := Cell.mkOrdinary (natToBits 0x65 8) #[]
private def revXTrunc7 : Cell := Cell.mkOrdinary (natToBits 0x64 7) #[]

private def revXGasBase : Int := computeExactGasBudget revXInstr
private def revXGasBaseMinusOne : Int := computeExactGasBudgetMinusOne revXInstr
private def revXPenaltyArg : Nat := 256
private def revXPenaltyGas : Int := revXGasBase + Int.ofNat (revXPenaltyArg - 255)
private def revXPenaltyGasMinusOne : Int := revXPenaltyGas - 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[revXInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := revXId
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
    instr := revXId
    codeCell? := some code
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
    instr := revXId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkNumTail (n : Nat) : Array Value :=
  List.range n |>.foldl (fun acc i => acc.push (intV (Int.ofNat i))) #[]

private def shortTail : Array Value :=
  #[(intV 11), .null, .cell Cell.empty, .slice (Slice.ofCell Cell.empty), .builder Builder.empty]

private def withXY (tail : Array Value) (x : Int) (y : Int) : Array Value :=
  (tail.push (intV x)).push (intV y)

private def withXYValues (tail : Array Value) (x : Value) (y : Value) : Array Value :=
  (tail.push x).push y

private def expectedReverseX (payload : Array Value) (x y : Nat) : Array Value :=
  let n : Nat := payload.size
  let total : Nat := x + y
  let front := payload.take (n - total)
  let revPart := payload.extract (n - total) (n - y)
  let top := payload.extract (n - y) n
  front ++ revPart.reverse ++ top

private def runRevXDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackReverseX revXInstr stack

private def runRevXDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackReverseX .add (VM.push (intV 777)) stack

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else
        pure s'

private def expectDecodeErr (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr instr} ({bits} bits)")

private def genRevXFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (baseCase, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/ok/noop/x0-y0" (withXY (mkNumTail 6) 0 0), rng1)
    else if shape = 1 then
      (mkCase "fuzz/ok/noop/x0-y2" (withXY (mkNumTail 8) 0 2), rng1)
    else if shape = 2 then
      (mkCase "fuzz/ok/reverse-top/x1" (withXY (mkNumTail 10) 1 0), rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/reverse-top/x2" (withXY (mkNumTail 12) 2 0), rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/no-surcharge/x255" (withXY (mkNumTail 260) 255 0), rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/reverse-middle/1-1" (withXY (mkNumTail 16) 1 1), rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/reverse-middle/4-3" (withXY (mkNumTail 24) 4 3), rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/reverse-middle/32-16" (withXY (mkNumTail 100) 32 16), rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/surcharge/x256-y0" (withXY (mkNumTail 300) 256 0), rng1)
    else if shape = 9 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 10 then
      (mkCase "fuzz/err/underflow-after-pop" (withXY (mkNumTail 4) 3 2), rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/y-type" (withXYValues (mkNumTail 4) (intV 7) (.cell Cell.empty)), rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/y-negative" (withXY (mkNumTail 4) 7 (-1)), rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/y-nan" (withXYValues (mkNumTail 4) (intV 7) (.int .nan)), rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/y-too-large" (withXY (mkNumTail 4) 7 (maxArg + 1)), rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/x-type" (withXYValues (mkNumTail 6) .null (intV 1)), rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/x-negative" (withXY (mkNumTail 6) (-1) 1), rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/x-nan" (withXYValues (mkNumTail 6) (.int .nan) (intV 1)), rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/x-too-large" (withXY (mkNumTail 6) (maxArg + 1) 1), rng1)
    else if shape = 19 then
      (mkCaseCode "fuzz/decode/neighbor-63" #[] revXNeighborBlkSwapX, rng1)
    else
      (mkCaseCode "fuzz/decode/trunc-7" #[] revXTrunc7, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)


def suite : InstrSuite where
  id := revXId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch-fallback"
          (runRevXDispatchFallback (withXY shortTail 1 1))
          ((withXY shortTail 1 1).push (intV 777)) },
    { name := "unit/runtime/underflow"
      run := do
        expectErr "underflow-empty" (runRevXDirect #[]) .stkUnd
        expectErr "underflow-after-y" (runRevXDirect (#[(intV 1)])) .stkUnd },
    { name := "unit/runtime/type-range"
      run := do
        expectErr "y-non-int" (runRevXDirect (withXYValues shortTail (intV 1) .null)) .typeChk
        expectErr "x-non-int" (runRevXDirect (withXYValues shortTail .null (intV 1))) .typeChk
        expectErr "y-negative" (runRevXDirect (withXY shortTail 5 (-1))) .rangeChk
        expectErr "x-negative" (runRevXDirect (withXY shortTail (-1) 5)) .rangeChk
        expectErr "y-nan" (runRevXDirect (withXYValues shortTail (intV 5) (.int .nan))) .rangeChk
        expectErr "x-nan" (runRevXDirect (withXYValues shortTail (.int .nan) (intV 5))) .rangeChk
        expectErr "y-too-large" (runRevXDirect (withXY shortTail 1 (maxArg + 1))) .rangeChk
        expectErr "x-too-large" (runRevXDirect (withXY shortTail (maxArg + 1) 1)) .rangeChk },
    { name := "unit/runtime/success-and-stack-shape"
      run := do
        expectOkStack "success/noop-x0-y2"
          (runRevXDirect (withXY (mkNumTail 6) 0 2))
          (expectedReverseX (mkNumTail 6) 0 2)
        expectOkStack "success/reverse-top-x3"
          (runRevXDirect (withXY (mkNumTail 6) 3 0))
          (expectedReverseX (mkNumTail 6) 3 0)
        expectOkStack "success/middle-2-2"
          (runRevXDirect (withXY (mkNumTail 8) 2 2))
          (expectedReverseX (mkNumTail 8) 2 2)
        expectErr "underflow-after-pops" (runRevXDirect (withXY (mkNumTail 3) 2 2)) .stkUnd },
    { name := "unit/encoding-and-decoding"
      run := do
        let code ←
          match assembleCp0 [revXInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/revx failed: {e}")
        if code.bits != natToBits 0x64 8 then
          throw (IO.userError s!"assemble/revx expected 0x64, got {code.bits}")
        let s0 := Slice.ofCell (Cell.mkOrdinary (natToBits 0x63 8 ++ natToBits 0x64 8 ++ natToBits 0x65 8) #[])
        let s1 ← expectDecodeStep "decode-63" s0 .blkSwapX 8
        let s2 ← expectDecodeStep "decode-64" s1 revXInstr 8
        let _ ← expectDecodeStep "decode-65" s2 .dropX 8
        expectDecodeErr "decode/truncated" revXTrunc7 } ]
  oracle := #[
    mkCase "oracle/fallback" (#[(intV 11), intV 22]) #[.add], -- [B1]
    mkCase "oracle/err/underflow-empty" #[], -- [B2]
    mkCase "oracle/err/underflow-after-y" #[(intV 1)], -- [B7]
    mkCase "oracle/err/y-type-null" (withXYValues (mkNumTail 6) (intV 7) .null), -- [B3]
    mkCase "oracle/err/y-type-cell" (withXYValues (mkNumTail 6) (intV 7) (.cell Cell.empty)), -- [B3]
    mkCase "oracle/err/y-negative" (withXY (mkNumTail 4) 2 (-1)), -- [B4]
    mkCase "oracle/err/y-negative-huge" (withXY (mkNumTail 4) 2 (-1024)), -- [B4]
    mkCase "oracle/err/y-too-large" (withXY (mkNumTail 4) 2 (maxArg + 1)), -- [B6]
    mkCase "oracle/err/x-type-slice" (withXYValues (mkNumTail 4) (.slice (Slice.ofCell Cell.empty)) (intV 1)), -- [B8]
    mkCase "oracle/err/x-type-builder" (withXYValues (mkNumTail 4) (.builder Builder.empty) (intV 1)), -- [B8]
    mkCase "oracle/err/x-negative" (withXY (mkNumTail 4) (-1) 1), -- [B9]
    mkCase "oracle/err/x-negative-large" (withXY (mkNumTail 4) (-123456) 1), -- [B9]
    mkCase "oracle/err/x-too-large" (withXY (mkNumTail 4) (maxArg + 1) 1), -- [B11]
    mkCase "oracle/err/underflow-after-pop" (withXY (mkNumTail 3) 2 2), -- [B12]
    mkCase "oracle/err/underflow-after-pop-boundary" (withXY (mkNumTail 5) 4 4), -- [B12]
    mkCase "oracle/ok/noop-x0-y1" (withXY (mkNumTail 8) 0 1), -- [B13]
    mkCase "oracle/ok/noop-x0-y10" (withXY (mkNumTail 12) 0 10), -- [B13]
    mkCase "oracle/ok/with-y0-x3" (withXY (mkNumTail 10) 3 0), -- [B14]
    mkCase "oracle/ok/with-y0-x5" (withXY (mkNumTail 12) 5 0), -- [B14]
    mkCase "oracle/ok/with-y0-x255" (withXY (mkNumTail 300) 255 0), -- [B14][B21]
    mkCase "oracle/ok/with-y0-x1" (withXY (mkNumTail 10) 1 0), -- [B14]
    mkCase "oracle/ok/middle-1-1" (withXY (mkNumTail 10) 1 1), -- [B15]
    mkCase "oracle/ok/middle-2-3" (withXY (mkNumTail 16) 2 3), -- [B15]
    mkCase "oracle/ok/middle-5-7" (withXY (mkNumTail 24) 5 7), -- [B15]
    mkCase "oracle/ok/middle-16-8" (withXY (mkNumTail 64) 16 8), -- [B15]
    mkCase "oracle/gas/base-exact"
      (withXY (mkNumTail 5) 0 1)
      #[.pushInt (.num revXGasBase), .tonEnvOp .setGasLimit, revXInstr]
      (oracleGasLimitsExact revXGasBase), -- [B21][B23]
    mkCase "oracle/gas/base-exact-minus-one"
      (withXY (mkNumTail 5) 0 1)
      #[.pushInt (.num revXGasBaseMinusOne), .tonEnvOp .setGasLimit, revXInstr]
      (oracleGasLimitsExactMinusOne revXGasBase), -- [B23]
    mkCaseWithProgram "oracle/gas/penalty-exact"
      (withXY (mkNumTail 300) (Int.ofNat revXPenaltyArg) 0)
      #[.pushInt (.num revXPenaltyGas), .tonEnvOp .setGasLimit, revXInstr]
      (oracleGasLimitsExact revXPenaltyGas), -- [B22][B23]
    mkCaseWithProgram "oracle/gas/penalty-exact-minus-one"
      (withXY (mkNumTail 300) (Int.ofNat revXPenaltyArg) 0)
      #[.pushInt (.num revXPenaltyGasMinusOne), .tonEnvOp .setGasLimit, revXInstr]
      (oracleGasLimitsExactMinusOne revXPenaltyGas), -- [B23]
    mkCase "oracle/asm/roundtrip-revx"
      (withXY (mkNumTail 3) 1 1), -- [B16][B17]
    mkCaseCode "oracle/decode/0x64" (mkNumTail 3) revXCode, -- [B18]
    mkCaseCode "oracle/decode/neighbor-left" #[] revXNeighborBlkSwapX, -- [B19]
    mkCaseCode "oracle/decode/neighbor-right" #[] revXNeighborDropX, -- [B19]
    mkCaseCode "oracle/decode/trunc7" #[] revXTrunc7 -- [B20]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr revXId
      count := 500
      gen := genRevXFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.REVX
