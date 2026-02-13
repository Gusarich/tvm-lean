import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.XCHG_0I_LONG

/-
INSTRUCTION: XCHG_0I_LONG

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path:
   - `execInstrStackXchg0` executes only on `.xchg0 idx`; all non-matching instructions forward to `next`.
2. [B2] Runtime long-form success branch:
   - `run` reaches `.xchg0 idx` then executes `VM.swap 0 idx` with `idx ≥ 16`.
   - Lean: both short and long handlers dispatch to the same VM primitive and mutate only positions 0 and `idx`.
   - C++: `exec_xchg0_l` checks underflow for `idx` and swaps `stack[0]` and `stack[idx]`.
3. [B3] Runtime underflow branch:
   - `VM.swap 0 idx` triggers `.stkUnd` when `idx ≥ stack.size` (via `check_underflow_p`).
4. [B4] Assembler branch:
   - `.xchg0 16..255` emits `0x11 ++ idx` (16 bits total).
   - `.xchg0 idx` with `idx < 16` is handled by `XCHG_0I` short form.
   - `.xchg0 >255` throws `.rangeChk`.
5. [B5] Decoder long-form branch:
   - `0x11 xx` decodes to `.xchg0 idx` and consumes 16 bits.
6. [B6] Decoder alias/truncation branches:
   - `0x10` decodes as `.xchg`, not `.xchg0`.
   - `0x11` without trailing byte is invalid and must throw `.invOpcode`.
   - 15-bit truncation of `0x11` is also invalid (`.invOpcode`).
7. [B7] Gas edges:
   - Long-form `xchg0` gas is `gasPerInstr + 16`.
   - Exact-gas budget should succeed; exact-minus-one should fail before execution.

TOTAL BRANCHES: 7
Each oracle test below is tagged with the branch(es) it covers.
-/

private def xchg0LongId : InstrId :=
  { name := "XCHG_0I_LONG" }

private def dispatchSentinel : Int := 13_137

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x5a 8) #[]

private def raw8 (w8 : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w8 8) #[]

private def xchg0LongCode (idx : Nat) : Cell :=
  Cell.mkOrdinary (natToBits 0x11 8 ++ natToBits idx 8) #[]

private def xchg0AliasCode : Cell :=
  Cell.mkOrdinary (natToBits 0x10 8 ++ natToBits 0x21 8) #[]

private def xchg0Trunc8 : Cell :=
  raw8 0x11

private def xchg0Trunc15 : Cell :=
  Cell.mkOrdinary (natToBits ((0x1100 : Nat) >>> 1) 15) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.xchg0 16])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xchg0LongId
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
    instr := xchg0LongId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkGasCase
    (name : String)
    (stack : Array Value)
    (idx : Nat)
    (budget : Int)
    (gasLimits : OracleGasLimits) : OracleCase :=
  { name := name
    instr := xchg0LongId
    initStack := stack
    program := #[.pushInt (.num budget), .tonEnvOp .setGasLimit, .xchg0 idx]
    gasLimits := gasLimits }

private def runXchg0LongDirect (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
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
      throw (IO.userError s!"{label}: expected assemble success, got {e}")
  | .ok got =>
      if got.bits == expected.bits && got.refs == expected.refs then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {reprStr expected.bits}, got {reprStr got.bits}")

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr)
    (expectedBits : Nat) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")
  | .ok (got, gotBits, rest) =>
      if got != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr got}")
      else if gotBits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {gotBits}")
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

private def xchg0LongGasExact : Int :=
  computeExactGasBudget (.xchg0 16)

private def xchg0LongGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.xchg0 16)

private def xchg0LongGasExactLimits : OracleGasLimits :=
  oracleGasLimitsExact xchg0LongGasExact

private def xchg0LongGasExactMinusOneLimits : OracleGasLimits :=
  oracleGasLimitsExactMinusOne xchg0LongGasExactMinusOne

private def mkDepthStack (n : Nat) : Array Value :=
  Array.range n |>.map (fun i => intV (Int.ofNat i))

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
      intV maxInt257
    else if k = 4 then
      intV minInt257
    else if k = 5 then
      .null
    else if k = 6 then
      .cell cellA
    else if k = 7 then
      .slice (Slice.ofCell cellB)
    else if k = 8 then
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

private def pickLongIdx (rng0 : StdGen) : Nat × StdGen :=
  pickFromPool #[16, 17, 31, 32, 63, 64, 127, 128, 191, 254, 255] rng0

private def pickBoundaryIdx (rng0 : StdGen) : Nat × StdGen :=
  pickFromPool #[16, 31, 127, 255] rng0

private def genXchg0LongFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  match shape with
  | 0 =>
    let (idx, rng2) := pickLongIdx rng1
    let (extra, rng3) := randNat rng2 0 3
    let size := idx + 1 + extra
    let (stack, rng4) := mkFuzzStack size rng3
    (mkCase (s!"fuzz/ok/long-success/{idx}") stack #[.xchg0 idx], rng4)
  | 1 =>
    let (idx, rng2) := pickLongIdx rng1
    let (size, rng3) := randNat rng2 (idx + 1) (idx + 5)
    let (stack, rng4) := mkFuzzStack size rng3
    (mkCase (s!"fuzz/ok/long-success/deep/{idx}") stack #[.xchg0 idx], rng4)
  | 2 =>
    let (idx, rng2) := pickBoundaryIdx rng1
    let (size, rng3) := randNat rng2 0 idx
    let (stack, rng4) := mkFuzzStack size rng3
    (mkCase (s!"fuzz/err/underflow/{idx}") stack #[.xchg0 idx], rng4)
  | 3 =>
    (mkCase "fuzz/err/asm/idx-256" #[intV 0] #[.xchg0 256], rng1)
  | 4 =>
    let (idx, rng2) := pickLongIdx rng1
    (mkCaseCode (s!"fuzz/raw/decode/long/{idx}") (mkDepthStack (idx + 1)) (xchg0LongCode idx), rng2)
  | 5 =>
    let (idx, rng2) := pickLongIdx rng1
    (mkCaseCode (s!"fuzz/raw/decode/long-noise/{idx}") (mkDepthStack (idx + 1)) (xchg0LongCode idx), rng2)
  | 6 =>
    (mkCaseCode "fuzz/raw/decode/alias-xchg" (mkDepthStack 4) xchg0AliasCode, rng1)
  | 7 =>
    let (tag, rng2) := randNat rng1 0 1
    let code :=
      if tag = 0 then
        xchg0Trunc8
      else
        xchg0Trunc15
    (mkCaseCode (if tag = 0 then "fuzz/raw/decode/trunc-8" else "fuzz/raw/decode/trunc-15") (mkDepthStack 2) code, rng2)
  | 8 =>
    (mkGasCase "fuzz/gas/exact" (mkDepthStack 256) 16 xchg0LongGasExact xchg0LongGasExactLimits, rng1)
  | 9 =>
    (mkGasCase "fuzz/gas/exact-minus-one" (mkDepthStack 256) 16 xchg0LongGasExactMinusOne xchg0LongGasExactMinusOneLimits, rng1)
  | 10 =>
    (mkCaseCode "fuzz/ok/raw/type-mix/long-255" (mkDepthStack 256) (xchg0LongCode 255), rng1)
  | _ =>
    let (tag, rng2) := randNat rng1 0 3
    let (idx, budget, gasLimits) :=
      if tag = 0 then
        (16, xchg0LongGasExact, xchg0LongGasExactLimits)
      else if tag = 1 then
        (16, xchg0LongGasExactMinusOne, xchg0LongGasExactMinusOneLimits)
      else if tag = 2 then
        (255, xchg0LongGasExact, xchg0LongGasExactLimits)
      else
        (255, xchg0LongGasExactMinusOne, xchg0LongGasExactMinusOneLimits)
    (mkGasCase (s!"fuzz/gas/explicit/{tag}") (mkDepthStack 256) idx budget gasLimits, rng2)

def suite : InstrSuite where
  id := xchg0LongId
  unit := #[
    { name := "unit/dispatch/fallback-to-next"
      run := do
        expectOkStack "dispatch/fallback-to-next"
          (runXchg0WithNext (.add) #[intV 10, intV 20, intV 30])
          #[intV dispatchSentinel, intV 10, intV 20, intV 30]
    },
    { name := "unit/dispatch/match-idx16"
      run := do
        expectOkStack "dispatch/match-idx16"
          (runXchg0LongDirect 16 (mkDepthStack 17))
          (expectedSwapTop 16 (mkDepthStack 17))
    },
    { name := "unit/runtime/long-success-type-mix"
      run := do
        let st : Array Value := #[
          intV 11, .null, .cell cellA, .builder Builder.empty, intV 55, .slice (Slice.ofCell cellB),
          intV 77, intV 88, intV 99, intV 111, intV 222, intV 333, intV 444, intV 555, intV 666, intV 777, intV 888, intV 999
        ]
        expectOkStack "runtime/long-success-type-mix" (runXchg0LongDirect 16 st) (expectedSwapTop 16 st)
    },
    { name := "unit/runtime/underflow-empty"
      run := do
        expectErr "runtime/underflow-empty" (runXchg0LongDirect 16 #[]) .stkUnd
    },
    { name := "unit/runtime/underflow-idx16-boundary"
      run := do
        expectErr "runtime/underflow-idx16-boundary" (runXchg0LongDirect 16 (mkDepthStack 16)) .stkUnd
    },
    { name := "unit/opcode/encode/idx16"
      run := do
        expectAssembledEq "opcode/encode/16" (.xchg0 16) (xchg0LongCode 16)
    },
    { name := "unit/opcode/encode/idx255"
      run := do
        expectAssembledEq "opcode/encode/255" (.xchg0 255) (xchg0LongCode 255)
    },
    { name := "unit/opcode/encode/idx256-range-error"
      run := do
        match assembleCp0 [(.xchg0 256)] with
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"opcode/encode/idx256-range-error: expected rangeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "opcode/encode/idx256-range-error: expected rangeChk, got success")
    },
    { name := "unit/decode/raw-11-10"
      run := do
        expectDecodeOk "decode/raw-11-10" (xchg0LongCode 16) (.xchg0 16) 16
    },
    { name := "unit/decode/raw-11-ff"
      run := do
        expectDecodeOk "decode/raw-11-ff" (xchg0LongCode 255) (.xchg0 255) 16
    },
    { name := "unit/decode/alias-xchg"
      run := do
        expectDecodeOk "decode/alias-xchg" xchg0AliasCode (.xchg 2 1) 16
    },
    { name := "unit/decode/truncated-8"
      run := do
        expectDecodeErr "decode/trunc-8" xchg0Trunc8 .invOpcode
    },
    { name := "unit/decode/truncated-15"
      run := do
        expectDecodeErr "decode/trunc-15" xchg0Trunc15 .invOpcode
    },
    { name := "unit/gas/limits-check"
      run := do
        if xchg0LongGasExactLimits.gasLimit != xchg0LongGasExact then
          throw (IO.userError s!"gas/limits-check: exact gas limit {xchg0LongGasExactLimits.gasLimit} != {xchg0LongGasExact}")
        if xchg0LongGasExactMinusOneLimits.gasLimit != xchg0LongGasExactMinusOne then
          throw (IO.userError s!"gas/limits-check: minus-one gas limit {xchg0LongGasExactMinusOneLimits.gasLimit} != {xchg0LongGasExactMinusOne}")
    }
  ]
  oracle := #[
    -- [B1]
    mkCase "oracle/dispatch/match-16" (mkDepthStack 17) #[.xchg0 16],
    -- [B1]
    mkCase "oracle/dispatch/match-255" (mkDepthStack 256) #[.xchg0 255],

    -- [B2]
    mkCase "oracle/ok/long/16-tight" (mkDepthStack 17) #[.xchg0 16],
    -- [B2]
    mkCase "oracle/ok/long/17" (mkDepthStack 18) #[.xchg0 17],
    -- [B2]
    mkCase "oracle/ok/long/31" (mkDepthStack 32) #[.xchg0 31],
    -- [B2]
    mkCase "oracle/ok/long/32" (mkDepthStack 33) #[.xchg0 32],
    -- [B2]
    mkCase "oracle/ok/long/63" (mkDepthStack 64) #[.xchg0 63],
    -- [B2]
    mkCase "oracle/ok/long/64" (mkDepthStack 65) #[.xchg0 64],
    -- [B2]
    mkCase "oracle/ok/long/127" (mkDepthStack 128) #[.xchg0 127],
    -- [B2]
    mkCase "oracle/ok/long/128" (mkDepthStack 129) #[.xchg0 128],
    -- [B2]
    mkCase "oracle/ok/long/191" (mkDepthStack 192) #[.xchg0 191],
    -- [B2]
    mkCase "oracle/ok/long/254" (mkDepthStack 255) #[.xchg0 254],
    -- [B2]
    mkCase "oracle/ok/long/255" (mkDepthStack 256) #[.xchg0 255],
    -- [B2]
    mkCase "oracle/ok/long/type-mix"
      #[intV 1, .null, .cell cellA, .builder Builder.empty, .slice (Slice.ofCell cellB), .cont (.quit 0), intV 2, intV 3, intV 4, intV 5, intV 6, intV 7, intV 8, intV 9, intV 10, intV 11, intV 12, intV 13, intV 14, intV 15] #[.xchg0 255],

    -- [B3]
    mkCase "oracle/err/underflow/idx16-size16" (#[]) #[.xchg0 16],
    -- [B3]
    mkCase "oracle/err/underflow/idx16-size15" (mkDepthStack 15) #[.xchg0 16],
    -- [B3]
    mkCase "oracle/err/underflow/idx31-size31" (mkDepthStack 31) #[.xchg0 31],
    -- [B3]
    mkCase "oracle/err/underflow/idx127-size127" (mkDepthStack 127) #[.xchg0 127],
    -- [B3]
    mkCase "oracle/err/underflow/idx255-size255" (mkDepthStack 255) #[.xchg0 255],

    -- [B4]
    mkCase "oracle/asm/long-16" (mkDepthStack 17) #[.xchg0 16],
    -- [B4]
    mkCase "oracle/asm/long-255" (mkDepthStack 256) #[.xchg0 255],
    -- [B4]
    mkCase "oracle/err/asm/idx256" (#[]) #[.xchg0 256],

    -- [B5]
    mkCaseCode "oracle/decode/long-16" (mkDepthStack 17) (xchg0LongCode 16),
    -- [B5]
    mkCaseCode "oracle/decode/long-17" (mkDepthStack 18) (xchg0LongCode 17),
    -- [B5]
    mkCaseCode "oracle/decode/long-31" (mkDepthStack 32) (xchg0LongCode 31),
    -- [B5]
    mkCaseCode "oracle/decode/long-255" (mkDepthStack 256) (xchg0LongCode 255),

    -- [B6]
    mkCaseCode "oracle/decode/alias-xchg" (mkDepthStack 4) xchg0AliasCode,
    -- [B6]
    mkCaseCode "oracle/decode/trunc-8" (#[]) xchg0Trunc8,
    -- [B6]
    mkCaseCode "oracle/decode/trunc-15" (#[]) xchg0Trunc15,

    -- [B7]
    mkGasCase "oracle/gas/exact" (mkDepthStack 256) 16 xchg0LongGasExact xchg0LongGasExactLimits,
    -- [B7]
    mkGasCase "oracle/gas/exact-minus-one" (mkDepthStack 256) 16 xchg0LongGasExactMinusOne xchg0LongGasExactMinusOneLimits,
    -- [B7]
    mkGasCase "oracle/gas/exact-255" (mkDepthStack 256) 255 xchg0LongGasExact xchg0LongGasExactLimits,
    -- [B7]
    mkGasCase "oracle/gas/exact-minus-one-255" (mkDepthStack 256) 255 xchg0LongGasExactMinusOne xchg0LongGasExactMinusOneLimits
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr xchg0LongId
      count := 500
      gen := genXchg0LongFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.XCHG_0I_LONG
