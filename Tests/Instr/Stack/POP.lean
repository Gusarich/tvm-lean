import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.POP

/-
INSTRUCTION: POP

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1, runtime normal] — short-form runtime path for `idx` in `0..15`: `VM.swap 0 idx`, then `VM.pop`, with exact stack-shape check
   via `VM.swap` (`max idx 0`); only enough-depth errors are possible.
2. [B2, runtime normal] — long-form runtime path for `idx` in `16..255`: same behavior as short runtime (`VM.swap` then `VM.pop`),
   no type checks and no data-path penalties.
3. [B3, runtime error] — underflow path (`.stkUnd`) whenever `idx >= stack.size` for either short or long form.
4. [B4, runtime property] — stack entries above the removed position are preserved in order.
5. [B5, runtime property] — no type/range checks on element values; `.null`, `.cell`, `.tuple`, `.builder`, `.cont` all pass untouched.
6. [B6, assembler] — if `idx <= 15`, `.pop idx` assembles to one byte `0x30 + idx`.
7. [B7, assembler] — if `16 <= idx <= 255`, `.pop idx` assembles to two bytes `0x57` then `idx`.
8. [B8, assembler] — `.pop 256` is rejected by `encodeCp0` with `.rangeChk`.
9. [B9, decoder] — short opcodes `0x30..0x3f` decode to `.pop 0..15`.
10. [B10, decoder] — long form `0x57` + byte decodes to `.pop byte`.
11. [B11, decoder] — invalid/truncated decode (e.g. empty/partial opcodes) reports `.invOpcode`.
12. [B12, gas accounting] — exact gas succeeds.
13. [B13, gas accounting] — exact-minus-one fails with out-of-gas behavior.

Gas note: POP has base cost only in `instrGas`; no variable gas penalty and no type/range penalties in execution.

TOTAL BRANCHES: 13

Each oracle test below is tagged with the branch(es) it covers.
-/

private def popId : InstrId := { name := "POP" }

private def repeatValue (v : Value) (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    let mut i : Nat := 0
    while i < n do
      out := out.push v
      i := i + 1
    return out

private def mkCase
    (name : String)
    (idx : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := popId
    program := #[.pop idx]
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := popId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def popProgram (idx : Nat) (gasLimit : Int) : Array Instr :=
  #[.pushInt (.num gasLimit), .tonEnvOp .setGasLimit, .pop idx]

private def runPopDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPop (.pop idx) stack

private def expectedPop (idx : Nat) (stack : Array Value) : Array Value :=
  if idx < stack.size then
    let pos : Nat := stack.size - 1 - idx
    (stack.extract 0 pos) ++ (stack.extract (pos + 1) stack.size)
  else
    stack

private def expectDecodeOk
    (label : String)
    (bits : BitString)
    (expected : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary bits #[])) with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, consumed, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr instr}")
      else if consumed != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {consumed}")
      else if rest.bitsRemaining != 0 then
        throw (IO.userError s!"{label}: expected stream fully consumed, remaining {rest.bitsRemaining}")
      else
        pure rest

private def expectDecodeErr (label : String) (bits : BitString) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary bits #[])) with
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (instr, consumed, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr instr} (bits={consumed})")

private def shortPopCode (idx : Nat) : Cell :=
  Cell.mkOrdinary (natToBits (0x30 + idx) 8) #[]

private def longPopCode (idx : Nat) : Cell :=
  Cell.mkOrdinary ((natToBits 0x57 8) ++ (natToBits idx 8)) #[]

private def popExactGas : Int :=
  computeExactGasBudget (.pop 0)

private def popExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne (.pop 0)

private def randomValue (rng0 : StdGen) : Value × StdGen :=
  let (shape, rng1) := randNat rng0 0 5
  if shape = 0 then
    let (x, rng2) := pickInt257Boundary rng1
    (intV x, rng2)
  else if shape = 1 then
    (.null, rng1)
  else if shape = 2 then
    (.cell Cell.empty, rng1)
  else if shape = 3 then
    (.tuple #[], rng1)
  else if shape = 4 then
    (.builder Builder.empty, rng1)
  else
    (.cont (.quit 0), rng1)

private def randomStack (len : Nat) (rng0 : StdGen) : Array Value × StdGen :=
  Id.run do
    let mut rng := rng0
    let mut out : Array Value := #[]
    let mut i : Nat := 0
    while i < len do
      let (v, rng') := randomValue rng
      out := out.push v
      rng := rng'
      i := i + 1
    return (out, rng)

private def genPopFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  if shape = 0 then
    let (x, rng2) := pickSigned257ish rng1
    let (y, rng3) := pickSigned257ish rng2
    (mkCase "fuzz/short/idx0-success" 0 #[intV x, intV y], rng3)
  else if shape = 1 then
    let (idx, rng2) := randNat rng1 1 15
    let (extra, rng3) := randNat rng2 0 4
    let depth := idx + 1 + extra
    let (stack, rng4) := randomStack depth rng3
    (mkCase s!"fuzz/short/idx-{idx}-variable-depth" idx stack, rng4)
  else if shape = 2 then
    let (extra, rng2) := randNat rng1 0 3
    let (stack, rng3) := randomStack (16 + extra) rng2
    (mkCase "fuzz/short/idx15/large-boundary" 15 stack, rng3)
  else if shape = 3 then
    let (idx, rng2) := randNat rng1 0 3
    let target : Nat := 16 + idx * 40
    let (extra, rng3) := randNat rng2 0 2
    let (stack, rng4) := randomStack (target + 1 + extra) rng3
    (mkCase (s!"fuzz/long/idx-{target}-success") target stack, rng4)
  else if shape = 4 then
    let (idx, rng2) := randNat rng1 16 255
    let (extra, rng3) := randNat rng2 0 3
    let depth : Nat := idx + 1 + extra
    let (stack, rng4) := randomStack depth rng3
    (mkCase "fuzz/long/boundary/variable" idx stack, rng4)
  else if shape = 5 then
    let (idx, rng2) := randNat rng1 0 15
    let (depth, rng3) := randNat rng2 0 (if idx = 0 then 0 else idx)
    let (stack, rng4) := randomStack depth rng3
    (mkCase (s!"fuzz/short/idx-{idx}/underflow") idx stack, rng4)
  else if shape = 6 then
    let (idx, rng2) := randNat rng1 16 255
    let (stackDepth, rng3) := randNat rng2 0 12
    let (stack, rng4) := randomStack stackDepth rng3
    (mkCase (s!"fuzz/long/idx-{idx}/underflow") idx stack, rng4)
  else if shape = 7 then
    let stack := repeatValue (intV 7) 256
    (mkCase "fuzz/long/idx255/long-stack" 255 stack, rng1)
  else if shape = 8 then
    let (x, rng2) := pickSigned257ish rng1
    let stack := #[intV 11, intV x, intV 12, intV 13]
    ({ name := "fuzz/gas/exact"
      instr := popId
      program := popProgram 0 popExactGas
      initStack := stack }, rng2)
  else
    let (x, rng2) := pickSigned257ish rng1
    let stack := #[intV 11, intV x, intV 12, intV 13]
    ({ name := "fuzz/gas/exact-minus-one"
      instr := popId
      program := popProgram 0 popExactGasMinusOne
      initStack := stack }, rng2)


def suite : InstrSuite where
  id := popId
  unit := #[
    { name := "unit/direct/short-pop-idx0"
      run := do
        let stack := #[intV 1, intV 2, intV 3]
        expectOkStack "unit/direct/short-pop-idx0" (runPopDirect 0 stack) (expectedPop 0 stack)
        let stack2 := #[intV 1, intV 2, intV 3, intV 4]
        expectOkStack "unit/direct/short-pop-idx1" (runPopDirect 1 stack2) (expectedPop 1 stack2)
        let stack3 := #[intV 1, intV 2, intV 3, intV 4, intV 5]
        expectOkStack "unit/direct/short-pop-idx3" (runPopDirect 3 stack3) (expectedPop 3 stack3) }
    ,
    { name := "unit/direct/long-pop-idx16"
      run := do
        let stack := repeatValue (intV 9) 17
        expectOkStack "unit/direct/long-pop-idx16" (runPopDirect 16 stack) (expectedPop 16 stack)
        let longStack := repeatValue (.cell Cell.empty) 200 ++ #[intV 1, intV 2, intV 3]
        expectOkStack "unit/direct/long-pop-idx128-type-preserve" (runPopDirect 128 longStack) (expectedPop 128 longStack) }
    ,
    { name := "unit/direct/underflow"
      run := do
        expectErr "unit/direct/underflow-empty" (runPopDirect 0 #[]) .stkUnd
        expectErr "unit/direct/underflow-one/idx0" (runPopDirect 0 #[intV 42]) .stkUnd
        expectErr "unit/direct/underflow-one/idx1" (runPopDirect 1 #[intV 42]) .stkUnd
        expectErr "unit/direct/underflow-16" (runPopDirect 16 (repeatValue (intV 0) 16)) .stkUnd
        expectErr "unit/direct/type-safe" (runPopDirect 1 #[.null, .cell Cell.empty, intV 7]) .stkUnd }
    ,
    { name := "unit/asm-encode-decode"
      run := do
        match assembleCp0 [.pop 0], assembleCp0 [.pop 1], assembleCp0 [.pop 15], assembleCp0 [.pop 16], assembleCp0 [.pop 255] with
        | .ok c0, .ok c1, .ok c15, .ok c16, .ok c255 =>
            if c0.bits != natToBits 0x30 8 then
              throw (IO.userError s!"unit/asm/encode/pop0 expected 0x30, got {c0.bits}")
            if c1.bits != natToBits 0x31 8 then
              throw (IO.userError s!"unit/asm/encode/pop1 expected 0x31, got {c1.bits}")
            if c15.bits != natToBits 0x3f 8 then
              throw (IO.userError s!"unit/asm/encode/pop15 expected 0x3f, got {c15.bits}")
            if c16.bits != (natToBits 0x57 8 ++ natToBits 16 8) then
              throw (IO.userError s!"unit/asm/encode/pop16 expected 0x57 0x10, got {c16.bits}")
            if c255.bits != (natToBits 0x57 8 ++ natToBits 255 8) then
              throw (IO.userError s!"unit/asm/encode/pop255 expected 0x57 0xff, got {c255.bits}")
            expectDecodeOk "unit/decode/pop0" (natToBits 0x30 8) (.pop 0) 8
            expectDecodeOk "unit/decode/pop1" (natToBits 0x31 8) (.pop 1) 8
            expectDecodeOk "unit/decode/pop15" (natToBits 0x3f 8) (.pop 15) 8
            expectDecodeOk "unit/decode/pop16" ((natToBits 0x57 8) ++ (natToBits 16 8)) (.pop 16) 16
            expectDecodeOk "unit/decode/pop255" ((natToBits 0x57 8) ++ (natToBits 255 8)) (.pop 255) 16
        | .error e, _, _, _, _ =>
            throw (IO.userError s!"unit/asm/encode/pop0 failed: {e}")
        | _, .error e, _, _, _ =>
            throw (IO.userError s!"unit/asm/encode/pop1 failed: {e}")
        | _, _, .error e, _, _ =>
            throw (IO.userError s!"unit/asm/encode/pop15 failed: {e}")
        | _, _, _, .error e, _ =>
            throw (IO.userError s!"unit/asm/encode/pop16 failed: {e}")
        | _, _, _, _, .error e =>
            throw (IO.userError s!"unit/asm/encode/pop255 failed: {e}") }
    ,
    { name := "unit/asm/encode/out-of-range"
      run := do
        match assembleCp0 [.pop 256] with
        | .error .rangeChk => pure ()
        | .ok c =>
            throw (IO.userError s!"unit/asm/encode/out-of-range expected rangeChk, got code {c.bits}")
        | .error e =>
            throw (IO.userError s!"unit/asm/encode/out-of-range got unexpected error: {e}") }
    ,
    { name := "unit/decode/truncated-invalid"
      run := do
        expectDecodeErr "unit/decode/truncated-4bits" (natToBits 0x3 4) .invOpcode
        expectDecodeErr "unit/decode/empty" #[] .invOpcode }
  ]
  oracle := #[
    -- [B1, B4, B5]
    mkCase "ok/short/idx0/remove-top" 0 #[intV 1, intV 2, intV 3],
    -- [B1, B4, B5]
    mkCase "ok/short/idx1/remove-mid" 1 #[intV 1, intV 2, intV 3],
    -- [B1, B4, B5]
    mkCase "ok/short/idx2/remove-lower" 2 #[intV 10, intV 20, intV 30],
    -- [B1, B4]
    mkCase "ok/short/idx4/mixed-values" 4 #[intV 1, .null, intV 2, .cell Cell.empty, intV 3, intV 4],
    -- [B1, B4, B5]
    mkCase "ok/short/idx7/noise" 7 #[intV 10, intV 11, intV 12, intV 13, intV 14, intV 15, intV 16, intV 17, intV 18],
    -- [B1, B4, B5]
    mkCase "ok/short/idx15/boundary-top" 15 (repeatValue (intV 7) 16),
    -- [B1, B4, B5]
    mkCase "ok/short/idx15/with-tail-preserved" 15 (#[intV 1, intV 2] ++ repeatValue (intV 3) 14 ++ #[.cell Cell.empty, .null]),
    -- [B1, B4, B5]
    mkCase "ok/short/idx10/nan-tolerant" 10 #[intV 1, .int .nan, intV 2, .null, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10],
    -- [B1, B4, B5]
    mkCase "ok/short/idx7/type-mix" 7 #[.null, .cell Cell.empty, .tuple #[], .builder Builder.empty, .cont (.quit 0), intV 1, intV 2, intV 3, intV 4],
    -- [B2, B4, B5]
    mkCase "ok/long/idx16/remove-top-of-long" 16 (repeatValue (intV 9) 17),
    -- [B2, B4, B5]
    mkCase "ok/long/idx16/mixed" 16 #[intV 1, .null, .cell Cell.empty, intV 4, intV 5, intV 6, .builder Builder.empty, intV 8, .tuple #[], intV 10, intV 11, intV 12, intV 13, intV 14, intV 15, intV 16, intV 17, intV 18],
    -- [B2, B4, B5]
    mkCase "ok/long/idx42/large" 42 (repeatValue (intV 1) 43),
    -- [B2, B4, B5]
    mkCase "ok/long/idx64/mixed" 64 (#[intV 11, .cell Cell.empty, intV 13, .null, intV 15, intV 16, .builder Builder.empty, intV 18, .tuple #[], intV 20, intV 21, .cont (.quit 0)] ++ repeatValue (intV 22) 54),
    -- [B2, B4, B5]
    mkCase "ok/long/idx128/deeper" 128 (repeatValue (intV 0) 129),
    -- [B2, B4, B5]
    mkCase "ok/long/idx255/bottom-removal" 255 (repeatValue (intV 2) 256),
    -- [B7, B8]
    mkCaseCode "decode/short/0x30" #[intV 1, intV 2, intV 3] (shortPopCode 0),
    -- [B7, B8]
    mkCaseCode "decode/short/0x31" #[intV 4, intV 5, intV 6] (shortPopCode 1),
    -- [B7, B8]
    mkCaseCode "decode/short/0x3f" (repeatValue (intV 8) 16) (shortPopCode 15),
    -- [B8]
    mkCaseCode "decode/long/0x57-00" #[intV 1, intV 2, intV 3] (longPopCode 0),
    -- [B8]
    mkCaseCode "decode/long/0x57-10" (repeatValue (intV 1) 17) (longPopCode 16),
    -- [B8]
    mkCaseCode "decode/long/0xff" (repeatValue (intV 5) 256) (longPopCode 255),
    -- [B3]
    mkCase "err/underflow-empty/idx0" 0 #[],
    -- [B3]
    mkCase "err/underflow-empty/idx15" 15 #[],
    -- [B3]
    mkCase "err/underflow-one-item/idx1" 1 #[intV 42],
    -- [B3]
    mkCase "err/underflow-two-item/idx2" 2 #[intV 1, intV 2],
    -- [B3]
    mkCase "err/underflow-three-item/idx3" 3 #[intV 1, intV 2, intV 3],
    -- [B3]
    mkCase "err/underflow/idx16-at-threshold" 16 (repeatValue (intV 1) 16),
    -- [B3]
    mkCase "err/underflow/idx255-at-threshold" 255 (repeatValue (intV 1) 255),
    -- [B12]
    { name := "ok/gas/exact"
      instr := popId
      program := popProgram 0 popExactGas
      initStack := #[intV 7, intV 8, intV 9] },
    -- [B13]
    { name := "err/gas/exact-minus-one"
      instr := popId
      program := popProgram 0 popExactGasMinusOne
      initStack := #[intV 7, intV 8, intV 9] },
    -- [B1, B4, B5]
    mkCase "ok/short/idx11/mix-long-tail" 11 #[intV 1, .null, .cell Cell.empty, intV 4, .builder Builder.empty, intV 6, .tuple #[], intV 8, intV 9, intV 10, intV 11, intV 12],
    -- [B2, B4, B5]
    mkCase "ok/long/idx64/mixed-tail" 64 (#[intV 1, .null, .cell Cell.empty, .builder Builder.empty, .tuple #[], intV 5] ++ repeatValue (intV 9) 59),
    -- [B1, B4, B5]
    mkCase "ok/short/idx5/with-cont" 5 #[intV 1, intV 2, intV 3, intV 4, intV 5, intV 6],
    -- [B3]
    mkCase "err/underflow/idx7/mixed" 7 #[.null, .cell Cell.empty, intV 1, .builder Builder.empty, intV 2]
  ]
  fuzz := #[
    { seed := 2026021302
      count := 500
      gen := genPopFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.POP
