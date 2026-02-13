import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.XCHG_0I

/-
INSTRUCTION: XCHG_0I

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path:
   - `execInstrStackXchg0` executes only on `.xchg0 idx`; all other instructions forward to `next`.
2. [B2] Valid runtime swap path:
   - Lean: `.xchg0 idx` calls `VM.swap 0 idx`.
   - C++: both `exec_xchg0` and `exec_xchg0_l` perform `check_underflow_p(idx)` then `swap(stack[0], stack[idx])`.
3. [B3] Runtime underflow path:
   - Lean: `check_underflow_p(idx)` fails with `stkUnd` when `idx ≥ stack.size`.
   - C++: same underflow check in `stack.check_underflow_p(x)`.
4. [B4] Assembler valid encoding branches:
   - `.xchg0 0` -> `0x00`
   - `.xchg0 1` -> `0x01`
   - `.xchg0 2..15` -> short single-byte opcodes
   - `.xchg0 16..255` -> `0x11` + `idx` byte
5. [B5] Assembler rejection branch:
   - `.xchg0` with `idx > 255` throws `rangeChk`.
6. [B6] Decoder branching:
   - `b8=0x00`, `0x01`, `0x02..0x0f` decode as `.xchg0`.
   - `b8=0x11` + byte decodes as `.xchg0 idx` (long form).
7. [B7] Decoder alias/truncation branches:
   - `b8=0x10` decodes as `.xchg`, not `.xchg0` (opcode aliasing).
   - `b8=0x11` without trailing byte is invalid and must throw `invOpcode`.
8. [B8] Gas edge for short opcode (8-bit): exact budget success and exact-minus-one failure.
9. [B9] Gas edge for long opcode (16-bit): exact budget success and exact-minus-one failure.

No type-check branches exist for `xchg0`; any value type is swappable.
TOTAL BRANCHES: 9
-/

private def xchg0Id : InstrId :=
  { name := "XCHG_0I" }

private def dispatchSentinel : Int := 13_137

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x5a 8) #[]

private def xchg0ShortCode (idx : Nat) : Cell :=
  Cell.mkOrdinary (natToBits idx 8) #[]

private def xchg0LongCode (idx : Nat) : Cell :=
  Cell.mkOrdinary (natToBits 0x11 8 ++ natToBits idx 8) #[]

private def xchgAliasCode : Cell :=
  Cell.mkOrdinary (natToBits 0x10 8 ++ natToBits 0x21 8) #[]

private def xchg0Trunc8 : Cell :=
  Cell.mkOrdinary (natToBits 0x11 8) #[]

private def xchg0Trunc15 : Cell :=
  Cell.mkOrdinary (natToBits ((0x1100 : Nat) >>> 1) 15) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.xchg0 0])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xchg0Id
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
    instr := xchg0Id
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def runXchg0Direct (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackXchg0 (.xchg0 idx) stack

private def runXchg0WithNext
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackXchg0 instr (VM.push (intV dispatchSentinel)) stack

private def expectedSwapTop (idx : Nat) (stack : Array Value) : Array Value :=
  match stack[0]?, stack[idx]? with
  | some top, some atIdx =>
      (stack.set! 0 atIdx).set! idx top
  | _, _ =>
      stack

private def expectAssembledEq
    (label : String)
    (instr : Instr)
    (expected : Cell) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      throw (IO.userError s!"{label}: assemble failed, got {reprStr e}")
  | .ok got =>
      if got.bits == expected.bits && got.refs == expected.refs then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {reprStr expected.bits}, got {reprStr got.bits}")

private def expectDecodeInstr
    (label : String)
    (code : Cell)
    (expected : Instr)
    (bits : Nat) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (got, gotBits, rest) =>
      if got != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr got}")
      else if gotBits != bits then
        throw (IO.userError s!"{label}: expected {bits} bits, got {gotBits}")
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
  | .ok (got, bits, _rest) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr got} ({bits} bits)")

private def xchg0GasExactShort : Int :=
  computeExactGasBudget (.xchg0 1)

private def xchg0GasExactShortMinusOne : Int :=
  computeExactGasBudgetMinusOne (.xchg0 1)

private def xchg0GasExactLong : Int :=
  computeExactGasBudget (.xchg0 16)

private def xchg0GasExactLongMinusOne : Int :=
  computeExactGasBudgetMinusOne (.xchg0 16)

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickFuzzValue (rng0 : StdGen) : Value × StdGen :=
  let (k, rng1) := randNat rng0 0 9
  let v : Value :=
    if k = 0 then
      intV 0
    else if k = 1 then
      intV 1
    else if k = 2 then
      intV (-1)
    else if k = 3 then
      intV 7
    else if k = 4 then
      intV maxInt257
    else if k = 5 then
      intV minInt257
    else if k = 6 then
      .null
    else if k = 7 then
      .cell cellA
    else if k = 8 then
      .slice (Slice.ofCell cellB)
    else if k = 9 then
      .builder Builder.empty
    else
      .cont (.quit 0)
  (v, rng1)

private def mkFuzzStack (n : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  let mut i : Nat := 0
  while i < n do
    let (v, rng') := pickFuzzValue rng
    out := out.push v
    rng := rng'
    i := i + 1
  return (out, rng)

private def pickXchg0ShortIdx (rng0 : StdGen) : Nat × StdGen :=
  pickFromPool #[0, 1, 2, 3, 7, 14, 15] rng0

private def pickXchg0LongIdx (rng0 : StdGen) : Nat × StdGen :=
  pickFromPool #[16, 17, 31, 32, 63, 64, 127, 128, 191, 254, 255] rng0

private def genXchg0FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    let (idx, rng2) := pickXchg0ShortIdx rng1
    let (extra, rng3) := randNat rng2 0 3
    let size : Nat := idx + 1 + extra
    let (stack, rng4) := mkFuzzStack size rng3
    ({ name := s!"fuzz/ok/short-success/{idx}", instr := xchg0Id, program := #[.xchg0 idx], initStack := stack }, rng4)
  else if shape = 1 then
    let (idx, rng2) := pickXchg0ShortIdx rng1
    let (depth, rng3) := randNat rng2 0 4
    let (stack, rng4) := mkFuzzStack (idx + 1 + depth) rng3
    ({ name := s!"fuzz/ok/short-success-mixed/{idx}", instr := xchg0Id, program := #[.xchg0 idx], initStack := stack }, rng4)
  else if shape = 2 then
    let (idx, rng2) := pickXchg0LongIdx rng1
    let (extra, rng3) := randNat rng2 0 3
    let size : Nat := idx + 1 + extra
    let (stack, rng4) := mkFuzzStack size rng3
    ({ name := s!"fuzz/ok/long-success/{idx}", instr := xchg0Id, program := #[.xchg0 idx], initStack := stack }, rng4)
  else if shape = 3 then
    let (idx, rng2) := pickXchg0LongIdx rng1
    let (stack, rng3) := mkFuzzStack (idx + 1) rng2
    ({ name := s!"fuzz/ok/long-tight/{idx}", instr := xchg0Id, program := #[.xchg0 idx], initStack := stack }, rng3)
  else if shape = 4 then
    let (idx, rng2) := pickFromPool #[1, 2, 7, 14, 15] rng1
    let (depth, rng3) := randNat rng2 0 idx
    let (stack, rng4) := mkFuzzStack depth rng3
    ({ name := s!"fuzz/err/underflow-short/{idx}", instr := xchg0Id, program := #[.xchg0 idx], initStack := stack }, rng4)
  else if shape = 5 then
    let (idx, rng2) := pickXchg0LongIdx rng1
    let (depth, rng3) := randNat rng2 0 200
    let (stack, rng4) := mkFuzzStack (Nat.min depth idx) rng3
    ({ name := s!"fuzz/err/underflow-long/{idx}", instr := xchg0Id, program := #[.xchg0 idx], initStack := stack }, rng4)
  else if shape = 6 then
    let (depth, rng2) := randNat rng1 0 6
    let (stack, rng3) := mkFuzzStack depth rng2
    ({ name := "fuzz/err/asm/idx-256", instr := xchg0Id, program := #[.xchg0 256], initStack := stack }, rng3)
  else if shape = 7 then
    let (idx, rng2) := pickXchg0ShortIdx rng1
    let (stack, rng3) := mkFuzzStack (idx + 1) rng2
    (mkCaseCode s!"fuzz/raw/decode/short/{idx}" stack (xchg0ShortCode idx), rng3)
  else if shape = 8 then
    let (idx, rng2) := pickXchg0LongIdx rng1
    let (stack, rng3) := mkFuzzStack (idx + 1) rng2
    (mkCaseCode s!"fuzz/raw/decode/long/{idx}" stack (xchg0LongCode idx), rng3)
  else if shape = 9 then
    let (tag, rng2) := randNat rng1 0 1
    let (stack, rng3) := mkFuzzStack (if tag = 0 then 1 else 2) rng2
    let code := if tag = 0 then xchg0Trunc8 else xchg0Trunc15
    (mkCaseCode (if tag = 0 then "fuzz/raw/err/decode-trunc-8" else "fuzz/raw/err/decode-trunc-15") stack code, rng3)
  else if shape = 10 then
    let (stack, rng2) := mkFuzzStack 3 rng1
    (mkCaseCode "fuzz/raw/decode/alias-xchg" stack xchgAliasCode, rng2)
  else
    let (tag, rng2) := randNat rng1 0 3
    let (budget, idx, depth) :=
      if tag = 0 then
        (xchg0GasExactShort, 1, 2)
      else if tag = 1 then
        (xchg0GasExactShortMinusOne, 1, 2)
      else if tag = 2 then
        (xchg0GasExactLong, 16, 256)
      else
        (xchg0GasExactLongMinusOne, 16, 256)
    let (stack, rng3) := mkFuzzStack depth rng2
    let case0 :
      OracleCase :=
      mkCase
        (if tag = 0 then "fuzz/gas/short-exact" else if tag = 1 then "fuzz/gas/short-minus-one" else if tag = 2 then "fuzz/gas/long-exact" else "fuzz/gas/long-minus-one")
        stack
        #[.pushInt (.num budget), .tonEnvOp .setGasLimit, .xchg0 idx]
    (case0, rng3)

def suite : InstrSuite where
  id := xchg0Id
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        let input := #[intV 7, intV 9]
        expectOkStack "unit/dispatch/fallback" (runXchg0WithNext (.pushInt (.num 1)) input) #[intV dispatchSentinel, intV 7, intV 9]
    },
    { name := "unit/dispatch/swap-path"
      run := do
        let input := #[intV 10, intV 20, intV 30]
        expectOkStack "unit/dispatch/swap-path" (runXchg0Direct 2 input) (expectedSwapTop 2 input)
    },
    { name := "unit/ok/idx0-idempotent"
      run := do
        let input := #[intV 1, intV 2, intV 3]
        expectOkStack "unit/ok/idx0-idempotent" (runXchg0Direct 0 input) input
    },
    { name := "unit/ok/idx1-swap"
      run := do
        expectOkStack "unit/ok/idx1-swap" (runXchg0Direct 1 #[intV 10, intV 20]) #[intV 20, intV 10]
    },
    { name := "unit/ok/idx15-boundary"
      run := do
        let input := Array.mkArray 16 (intV 1)
        expectOkStack "unit/ok/idx15-boundary" (runXchg0Direct 15 input) (expectedSwapTop 15 input)
    },
    { name := "unit/ok/idx16-long-form"
      run := do
        let input := Array.mkArray 17 (intV 42)
        expectOkStack "unit/ok/idx16-long-form" (runXchg0Direct 16 input) (expectedSwapTop 16 input)
    },
    { name := "unit/ok/mixed-types"
      run := do
        let input := #[.null, .cell cellA, .builder Builder.empty, intV 7, .cont (.quit 0)]
        expectOkStack "unit/ok/mixed-types" (runXchg0Direct 3 input) (expectedSwapTop 3 input)
    },
    { name := "unit/err/underflow-empty"
      run := do
        expectErr "unit/err/underflow-empty" (runXchg0Direct 2 #[]) .stkUnd
    },
    { name := "unit/err/underflow-short"
      run := do
        expectErr "unit/err/underflow-short" (runXchg0Direct 15 #[intV 1, intV 2, intV 3]) .stkUnd
    },
    { name := "unit/err/underflow-long"
      run := do
        expectErr "unit/err/underflow-long" (runXchg0Direct 16 (Array.mkArray 15 (intV 1))) .stkUnd
    },
    { name := "unit/opcode/encode-boundaries"
      run := do
        expectAssembledEq "unit/opcode/encode/00" (.xchg0 0) (xchg0ShortCode 0)
        expectAssembledEq "unit/opcode/encode/01" (.xchg0 1) (xchg0ShortCode 1)
        expectAssembledEq "unit/opcode/encode/0f" (.xchg0 15) (xchg0ShortCode 15)
        expectAssembledEq "unit/opcode/encode/10" (.xchg0 16) (xchg0LongCode 16)
        expectAssembledEq "unit/opcode/encode/ff" (.xchg0 255) (xchg0LongCode 255)
    },
    { name := "unit/opcode/encode-range-error"
      run := do
        match assembleCp0 [(.xchg0 256)] with
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"unit/opcode/encode-range-error: expected rangeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "unit/opcode/encode-range-error: expected rangeChk, got success")
    },
    { name := "unit/opcode/decode/short"
      run := do
        expectDecodeInstr "unit/opcode/decode/00" (xchg0ShortCode 0) (.xchg0 0) 8
        expectDecodeInstr "unit/opcode/decode/01" (xchg0ShortCode 1) (.xchg0 1) 8
        expectDecodeInstr "unit/opcode/decode/0f" (xchg0ShortCode 15) (.xchg0 15) 8
    },
    { name := "unit/opcode/decode/long"
      run := do
        expectDecodeInstr "unit/opcode/decode/11-00" (xchg0LongCode 0) (.xchg0 0) 16
        expectDecodeInstr "unit/opcode/decode/11-ff" (xchg0LongCode 255) (.xchg0 255) 16
    },
    { name := "unit/opcode/decode/alias-and-truncation"
      run := do
        expectDecodeInstr "unit/opcode/decode/alias-xchg" xchgAliasCode (.xchg 2 1) 16
        expectDecodeErr "unit/opcode/decode/truncated-8" xchg0Trunc8 .invOpcode
        expectDecodeErr "unit/opcode/decode/truncated-15" xchg0Trunc15 .invOpcode
    }
  ]
  oracle := #[
    -- [B2]
    mkCase "ok/short/idx0-idempotent" #[intV 7],
    -- [B2]
    mkCase "ok/short/idx1" #[intV 10, intV 20] (#[.xchg0 1]),
    -- [B2]
    mkCase "ok/short/idx2-mixed" #[intV 1, .null, .cell cellA] (#[.xchg0 2]),
    -- [B2]
    mkCase "ok/short/idx3" (Array.mkArray 4 (intV 3)) (#[.xchg0 3]),
    -- [B2]
    mkCase "ok/short/idx7" #[.null, .cell cellA, intV 3, intV 4, intV 5, .tuple #[], .builder Builder.empty, intV 7] (#[.xchg0 7]),
    -- [B2]
    mkCase "ok/short/idx9" (Array.mkArray 10 (intV 9)) (#[.xchg0 9]),
    -- [B2]
    mkCase "ok/short/idx14/with-boundary-types" #[.cell cellA, intV 1, .null, .slice (Slice.ofCell cellB), .tuple #[], .cont (.quit 0), intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10, intV 11, intV 12] (#[.xchg0 14]),

    -- [B2]
    mkCase "ok/long/idx16-tight" (Array.mkArray 17 (intV 16)) (#[.xchg0 16]),
    -- [B2]
    mkCase "ok/long/idx17" (Array.mkArray 18 (intV 17)) (#[.xchg0 17]),
    -- [B2]
    mkCase "ok/long/idx31" (Array.mkArray 32 (intV 31)) (#[.xchg0 31]),
    -- [B2]
    mkCase "ok/long/idx32" (Array.mkArray 33 (intV 32)) (#[.xchg0 32]),
    -- [B2]
    mkCase "ok/long/idx63" (Array.mkArray 64 (intV 63)) (#[.xchg0 63]),
    -- [B2]
    mkCase "ok/long/idx64" (Array.mkArray 65 (intV 64)) (#[.xchg0 64]),
    -- [B2]
    mkCase "ok/long/idx127" (Array.mkArray 128 (intV 127)) (#[.xchg0 127]),
    -- [B2]
    mkCase "ok/long/idx128" (Array.mkArray 129 (intV 128)) (#[.xchg0 128]),
    -- [B2]
    mkCase "ok/long/idx191" (Array.mkArray 192 (intV 191)) (#[.xchg0 191]),
    -- [B2]
    mkCase "ok/long/idx254" (Array.mkArray 255 (intV 254)) (#[.xchg0 254]),
    -- [B2]
    mkCase "ok/long/idx255" (Array.mkArray 256 (intV 255)) (#[.xchg0 255]),
    -- [B2]
    mkCase "ok/long/idx255-with-noise" #[intV 1, .null, .cell cellA, .builder Builder.empty, .slice (Slice.ofCell cellB), .cont (.quit 0), intV 2, intV 3, intV 4] (#[.xchg0 255]),

    -- [B3]
    mkCase "err/underflow-empty" #[],
    -- [B3]
    mkCase "err/underflow-one" #[intV 7],
    -- [B3]
    mkCase "err/underflow-two" #[intV 7, intV 8],
    -- [B3]
    mkCase "err/underflow-short-boundary" #[intV 1, intV 2, intV 3, intV 4, intV 5] (#[.xchg0 15]),
    -- [B3]
    mkCase "err/underflow-long-boundary" (Array.mkArray 16 (intV 1)) (#[.xchg0 16]),
    -- [B3]
    mkCase "err/underflow-long-half-depth" (Array.mkArray 127 (intV 1)) (#[.xchg0 255]),


    -- [B6]
    mkCaseCode "ok/raw-decode/00" #[intV 77] (xchg0ShortCode 0),
    -- [B6]
    mkCaseCode "ok/raw-decode/01" #[intV 77, intV 88] (xchg0ShortCode 1),
    -- [B6]
    mkCaseCode "ok/raw-decode/0f" (Array.mkArray 16 (intV 9)) (xchg0ShortCode 15),
    -- [B6]
    mkCaseCode "ok/raw-decode/11-00" #[intV 1] (xchg0LongCode 0),
    -- [B6]
    mkCaseCode "ok/raw-decode/11-ff" (Array.mkArray 256 (intV 1)) (xchg0LongCode 255),

    -- [B7]
    mkCaseCode "ok/raw-decode/alias-xchg" (Array.mkArray 3 (intV 1)) xchgAliasCode,
    -- [B7]
    mkCaseCode "err/raw-decode/truncated-8" #[] xchg0Trunc8,
    -- [B7]
    mkCaseCode "err/raw-decode/truncated-15" #[] xchg0Trunc15,

    -- [B8]
    mkCase "gas/short/exact" (Array.mkArray 2 (intV 7)) #[.pushInt (.num xchg0GasExactShort), .tonEnvOp .setGasLimit, .xchg0 1],
    -- [B8]
    mkCase "gas/short/exact-minus-one" (Array.mkArray 2 (intV 7)) #[.pushInt (.num xchg0GasExactShortMinusOne), .tonEnvOp .setGasLimit, .xchg0 1],
    -- [B9]
    mkCase "gas/long/exact" (Array.mkArray 256 (intV 7)) #[.pushInt (.num xchg0GasExactLong), .tonEnvOp .setGasLimit, .xchg0 16],
    -- [B9]
    mkCase "gas/long/exact-minus-one" (Array.mkArray 256 (intV 7)) #[.pushInt (.num xchg0GasExactLongMinusOne), .tonEnvOp .setGasLimit, .xchg0 16],
    -- [B2, B9]
    mkCase "ok/long/gas-tight/idx16" (Array.mkArray 17 (intV 16)) #[.pushInt (.num xchg0GasExactLong), .tonEnvOp .setGasLimit, .xchg0 16]
  ]
  fuzz := #[
    { seed := 2026021307
      count := 500
      gen := genXchg0FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.XCHG_0I
