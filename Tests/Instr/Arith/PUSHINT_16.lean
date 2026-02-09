import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.PUSHINT_16

/-
PUSHINT_16 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0x81` decode to `.pushInt (.num ...)`)
  - `TvmLean/Semantics/Exec/Stack/PushInt.lean` (`execInstrStackPushInt`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`pushIntQuiet`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`register_int_const_ops`, `exec_push_smallint` bound to opcode `0x81`).

Branch counts used for this suite:
- Lean: 5 branch points / 7 terminal outcomes
  (decode dispatch to `0x81` vs other opcodes; truncated-arg `invOpcode` vs success;
   signed-16 two's-complement split; handler dispatch `.pushInt` vs `next`;
   generic `.pushInt` execution split `.nan`/`.num` with `pushIntQuiet` success vs `intOv`).
- C++: 3 branch points / 5 aligned terminal outcomes
  (opcode table dispatch to `0x81`; decode-length guard for 16-bit arg; `exec_push_smallint`
   sign extension and stack push).

Key risk areas covered:
- signed-16 decode boundaries (`0x7fff`, `0x8000`, `0xffff`);
- width routing around tiny/short/long cutoffs (`127`, `128`, `32767`, `32768`);
- stack preservation for below-top values after successful push;
- oracle prelude injection rules for non-serializable prefix values (NaN/out-of-range);
- exact gas cliff for `PUSHINT budget; SETGASLIMIT; PUSHINT_16`.
-/

private def pushInt16Id : InstrId := { name := "PUSHINT_16" }

private def pushInt16GasProbe : Int := 1024

private def pushInt16GasProbeInstr : Instr := .pushInt (.num pushInt16GasProbe)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pushInt16Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkPushInt16Case
    (name : String)
    (imm16 : Int)
    (stack : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[.pushInt (.num imm16)] gasLimits fuel

private def mkPushInt16CaseFromIntVals
    (name : String)
    (prefixVals : Array IntVal)
    (imm16 : Int)
    (programTail : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, prelude) := oracleIntInputsToStackOrProgram prefixVals
  mkCase name stack (prelude ++ #[.pushInt (.num imm16)] ++ programTail) gasLimits fuel

private def runPushIntDirect (x : IntVal) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPushInt (.pushInt x) stack

private def runPushInt16Direct (imm16 : Int) (stack : Array Value) : Except Excno (Array Value) :=
  runPushIntDirect (.num imm16) stack

private def runPushIntDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPushInt .add (VM.push (intV 909)) stack

private def failUnit (msg : String) : IO α :=
  throw (IO.userError msg)

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      failUnit s!"{label}: decode failed with {e}"
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        failUnit s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}"
      else if bits != expectedBits then
        failUnit s!"{label}: expected bits {expectedBits}, got {bits}"
      else
        pure s'

private def expectDecodeErr (label : String) (s : Slice) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .ok (instr, bits, _) =>
      failUnit s!"{label}: expected decode error {expected}, got {reprStr instr} ({bits} bits)"
  | .error e =>
      if e = expected then
        pure ()
      else
        failUnit s!"{label}: expected decode error {expected}, got {e}"

private def expectPushIntDecodeBits
    (label : String)
    (x : Int)
    (expectedBits : Nat) : IO Unit := do
  match assembleCp0 [Instr.pushInt (.num x)] with
  | .error e =>
      failUnit s!"{label}: assemble failed with {e}"
  | .ok code =>
      match decodeCp0WithBits (Slice.ofCell code) with
      | .error e =>
          failUnit s!"{label}: decode failed with {e}"
      | .ok (.pushInt (.num y), bits, s') =>
          if y != x then
            failUnit s!"{label}: expected immediate {x}, got {y}"
          else if bits != expectedBits then
            failUnit s!"{label}: expected bits {expectedBits}, got {bits}"
          else if s'.bitsRemaining != 0 then
            failUnit s!"{label}: expected exhausted slice, got {s'.bitsRemaining} bits remaining"
          else
            pure ()
      | .ok (.pushInt .nan, bits, _) =>
          failUnit s!"{label}: expected numeric PUSHINT decode, got PUSHNAN ({bits} bits)"
      | .ok (instr, bits, _) =>
          failUnit s!"{label}: expected PUSHINT decode, got {reprStr instr} ({bits} bits)"

private def rawPushInt16Cell (imm16Word : Nat) : Cell :=
  let bits := natToBits 0x81 8 ++ natToBits imm16Word 16 ++ Array.replicate 8 false
  Cell.mkOrdinary bits #[]

private def expectDecodedPushInt16Word
    (label : String)
    (imm16Word : Nat)
    (expected : Int) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell (rawPushInt16Cell imm16Word)) with
  | .error e =>
      failUnit s!"{label}: decode failed with {e}"
  | .ok (.pushInt (.num n), bits, s') =>
      if n != expected then
        failUnit s!"{label}: expected immediate {expected}, got {n}"
      else if bits != 24 then
        failUnit s!"{label}: expected 24 decoded bits, got {bits}"
      else if s'.bitsRemaining != 8 then
        failUnit s!"{label}: expected 8 tail bits, got {s'.bitsRemaining}"
      else
        pure ()
  | .ok (.pushInt .nan, bits, _) =>
      failUnit s!"{label}: expected numeric PUSHINT decode, got PUSHNAN ({bits} bits)"
  | .ok (instr, bits, _) =>
      failUnit s!"{label}: expected PUSHINT decode, got {reprStr instr} ({bits} bits)"

private def pushInt16SetGasExact : Int :=
  computeExactGasBudget pushInt16GasProbeInstr

private def pushInt16SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pushInt16GasProbeInstr

private def pushInt16BoundaryPool : Array Int :=
  #[-32768, -32767, -1024, -256, -129, 128, 256, 1024, 32766, 32767]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def coerceToNonTiny16 (n : Int) : Int :=
  if (-128 ≤ n ∧ n ≤ 127) then
    if n < 0 then n - 128 else n + 128
  else
    n

private def pickPushInt16Uniform (rng : StdGen) : Int × StdGen :=
  let (u, rng') := randNat rng 0 65535
  let n := natToIntSignedTwos u 16
  (coerceToNonTiny16 n, rng')

private def pickPushInt16Boundary (rng : StdGen) : Int × StdGen :=
  pickFromPool pushInt16BoundaryPool rng

private def pickPushInt16Mixed (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickPushInt16Boundary rng1
  else
    pickPushInt16Uniform rng1

private def genPushInt16FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (case0, rng2) :=
    if shape = 0 then
      let (imm, r2) := pickPushInt16Boundary rng1
      (mkPushInt16Case s!"fuzz/shape-{shape}/ok/boundary-empty" imm, r2)
    else if shape = 1 then
      let (imm, r2) := pickPushInt16Mixed rng1
      (mkPushInt16Case s!"fuzz/shape-{shape}/ok/random-empty" imm, r2)
    else if shape = 2 then
      let (imm, r2) := pickPushInt16Mixed rng1
      let (x, r3) := pickSigned257ish r2
      (mkPushInt16Case s!"fuzz/shape-{shape}/ok/one-int-understack" imm #[intV x], r3)
    else if shape = 3 then
      let (imm, r2) := pickPushInt16Mixed rng1
      let (x, r3) := pickSigned257ish r2
      let (pick, r4) := randNat r3 0 1
      let below : Value := if pick = 0 then .null else .cell Cell.empty
      (mkPushInt16Case s!"fuzz/shape-{shape}/ok/mixed-understack" imm #[below, intV x], r4)
    else if shape = 4 then
      let (imm, r2) := pickPushInt16Mixed rng1
      let (x, r3) := pickSigned257ish r2
      let (y, r4) := pickInt257Boundary r3
      (mkPushInt16CaseFromIntVals s!"fuzz/shape-{shape}/prelude/serializable-prefix" #[.num x, .num y] imm, r4)
    else if shape = 5 then
      let (imm, r2) := pickPushInt16Mixed rng1
      let (x, r3) := pickSigned257ish r2
      (mkPushInt16CaseFromIntVals s!"fuzz/shape-{shape}/prelude/nan-prefix" #[.num x, .nan] imm, r3)
    else if shape = 6 then
      let (imm, r2) := pickPushInt16Mixed rng1
      let (oor, r3) := pickInt257OutOfRange r2
      (mkPushInt16CaseFromIntVals s!"fuzz/shape-{shape}/prelude/out-of-range-prefix" #[.num oor] imm, r3)
    else if shape = 7 then
      (mkCase s!"fuzz/shape-{shape}/gas/exact" #[]
        #[.pushInt (.num pushInt16SetGasExact), .tonEnvOp .setGasLimit, pushInt16GasProbeInstr], rng1)
    else if shape = 8 then
      (mkCase s!"fuzz/shape-{shape}/gas/exact-minus-one" #[]
        #[.pushInt (.num pushInt16SetGasExactMinusOne), .tonEnvOp .setGasLimit, pushInt16GasProbeInstr], rng1)
    else
      let (imm, r2) := pickPushInt16Mixed rng1
      let (x, r3) := pickSigned257ish r2
      let (y, r4) := pickSigned257ish r3
      (mkPushInt16Case s!"fuzz/shape-{shape}/ok/deep-stack" imm #[.null, intV x, .cell Cell.empty, intV y], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := pushInt16Id
  unit := #[
    { name := "unit/direct/pushes-immediate-and-preserves-understack"
      run := do
        expectOkStack "empty/min" (runPushInt16Direct (-32768) #[]) #[intV (-32768)]
        expectOkStack "empty/max" (runPushInt16Direct 32767 #[]) #[intV 32767]
        expectOkStack "int-understack" (runPushInt16Direct 1024 #[intV 7]) #[intV 7, intV 1024]
        expectOkStack "mixed-understack" (runPushInt16Direct (-1024) #[.null, .cell Cell.empty])
          #[.null, .cell Cell.empty, intV (-1024)] }
    ,
    { name := "unit/decode/raw-opcode-0x81-sign-extension-and-truncation"
      run := do
        expectDecodedPushInt16Word "decode/0x0000" 0x0000 0
        expectDecodedPushInt16Word "decode/0x0001" 0x0001 1
        expectDecodedPushInt16Word "decode/0x7fff" 0x7fff 32767
        expectDecodedPushInt16Word "decode/0x8000" 0x8000 (-32768)
        expectDecodedPushInt16Word "decode/0xffff" 0xffff (-1)
        let shortCell := Cell.mkOrdinary (natToBits 0x81 8 ++ natToBits 0xab 8) #[]
        expectDecodeErr "decode/truncated-imm16" (Slice.ofCell shortCell) .invOpcode }
    ,
    { name := "unit/encoding/width-routing-boundaries"
      run := do
        expectPushIntDecodeBits "encode/tiny-max-127" 127 16
        expectPushIntDecodeBits "encode/tiny-min-neg128" (-128) 16
        expectPushIntDecodeBits "encode/pushint16-min-neg129" (-129) 24
        expectPushIntDecodeBits "encode/pushint16-max-pos128" 128 24
        expectPushIntDecodeBits "encode/pushint16-min" (-32768) 24
        expectPushIntDecodeBits "encode/pushint16-max" 32767 24
        expectPushIntDecodeBits "encode/long-after-window-pos32768" 32768 13
        expectPushIntDecodeBits "encode/long-after-window-neg32769" (-32769) 13 }
    ,
    { name := "unit/prelude-injection/serialization-rules"
      run := do
        let (stackSer, progSer) := oracleIntInputsToStackOrProgram #[.num 9, .num (-7)]
        if stackSer != #[intV 9, intV (-7)] then
          failUnit s!"serializable stack mismatch: got {reprStr stackSer}"
        else if !progSer.isEmpty then
          failUnit s!"serializable prelude expected empty, got {reprStr progSer}"
        let (stackNan, progNan) := oracleIntInputsToStackOrProgram #[.num 9, .nan]
        if !stackNan.isEmpty then
          failUnit s!"nan prelude stack expected empty, got {reprStr stackNan}"
        else if progNan != #[.pushInt (.num 9), .pushInt .nan] then
          failUnit s!"nan prelude mismatch: got {reprStr progNan}"
        let oor := maxInt257 + 1
        let (stackOor, progOor) := oracleIntInputsToStackOrProgram #[.num oor]
        if !stackOor.isEmpty then
          failUnit s!"out-of-range prelude stack expected empty, got {reprStr stackOor}"
        else if progOor != #[.pushInt (.num oor)] then
          failUnit s!"out-of-range prelude mismatch: got {reprStr progOor}" }
    ,
    { name := "unit/dispatch/non-pushint-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runPushIntDispatchFallback #[]) #[intV 909] }
    ,
    { name := "unit/generic-pushint/overflow-branch-still-intov"
      run := do
        expectErr "overflow/max+1" (runPushIntDirect (.num (maxInt257 + 1)) #[]) .intOv
        expectErr "overflow/min-1" (runPushIntDirect (.num (minInt257 - 1)) #[]) .intOv
        expectOkStack "pushnan" (runPushIntDirect .nan #[intV 5]) #[intV 5, .int .nan] }
  ]
  oracle := #[
    mkPushInt16Case "ok/empty/min-int16" (-32768),
    mkPushInt16Case "ok/empty/max-int16" 32767,
    mkPushInt16Case "ok/empty/positive-mid" 1024,
    mkPushInt16Case "ok/empty/negative-mid" (-1024),
    mkPushInt16Case "ok/preserve/one-int-understack" 2048 #[intV 7],
    mkPushInt16Case "ok/preserve/non-int-understack" (-2048) #[.null],
    mkPushInt16Case "ok/preserve/mixed-understack" 30000 #[.cell Cell.empty, intV (-5), .null],
    mkPushInt16Case "boundary/lowest-non-tiny-neg129" (-129),
    mkPushInt16Case "boundary/lowest-non-tiny-pos128" 128,
    mkPushInt16CaseFromIntVals "prelude/serializable-prefix-stays-initstack"
      #[.num 7, .num (-8)] 4096,
    mkPushInt16CaseFromIntVals "prelude/nan-prefix-injected-before-pushint16"
      #[.num 7, .nan] 4096,
    mkPushInt16CaseFromIntVals "prelude/nan-only-prefix"
      #[.nan] 2048,
    mkPushInt16CaseFromIntVals "prelude/out-of-range-prefix-intov-before-pushint16"
      #[.num (maxInt257 + 1)] 1024,
    mkPushInt16CaseFromIntVals "prelude/nan-then-out-of-range-intov-before-pushint16"
      #[.nan, .num (maxInt257 + 1)] 1024,
    mkCase "gas/exact-cost-succeeds" #[]
      #[.pushInt (.num pushInt16SetGasExact), .tonEnvOp .setGasLimit, pushInt16GasProbeInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[]
      #[.pushInt (.num pushInt16SetGasExactMinusOne), .tonEnvOp .setGasLimit, pushInt16GasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020816
      count := 600
      gen := genPushInt16FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.PUSHINT_16
