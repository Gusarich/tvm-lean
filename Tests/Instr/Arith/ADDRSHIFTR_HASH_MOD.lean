import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.ADDRSHIFTR_HASH_MOD

/-
ADDRSHIFTR#MOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false true 3 0 false (some z)` specialization,
     add-compat quotient path `rshiftPow2RoundAddCompat` and remainder `modPow2Round`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate SHR/MOD family `0xa930..0xa932`, `z ∈ [1, 256]`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, `0xa930..0xa932` decode to `.shrMod false true 3 ... (some z)`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`, underflow/type behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`mul=false`, `add=true`, `d=3`, `roundMode=0`, `quiet=false`, `zOpt=some z`):
- Lean specialization: 7 branch sites / 9 terminal outcomes
  (dispatch/fallback; depth gate; `w` pop type; `x` pop type; numeric-vs-invalid split;
   quotient push fit-vs-`intOv`; remainder push fit-vs-`intOv`).
- C++ specialization: 6 branch sites / 9 aligned terminal outcomes
  (`check_underflow(2)`; const-shift decode route; `pop_int` for `w` then `x`;
   invalid-input funnel; quotient and remainder push fit-vs-overflow).

Key risk areas covered:
- hash-immediate shift is encoded (no runtime shift pop), so pop order is `w` then `x`;
- explicit underflow/type error ordering for depth 0/1 and non-int operand shapes;
- NaN and out-of-range integer injection occurs via `PUSHINT` prelude only;
- boundary shifts `z=1` and `z=256`, plus CP0 decode/encode behavior;
- exact gas cliff with `PUSHINT n; SETGASLIMIT; ADDRSHIFTR#MOD`.
-/

private def addrShiftRHashModId : InstrId := { name := "ADDRSHIFTR#MOD" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkAddrShiftRHashModInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod false true 3 0 false (some shift))

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := addrShiftRHashModId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkShiftCase
    (name : String)
    (shift : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[mkAddrShiftRHashModInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkAddrShiftRHashModInstr shift
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix.push instr) gasLimits fuel

private def runAddrShiftRHashModDirect (shift : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkAddrShiftRHashModInstr shift) stack

private def runAddrShiftRHashModDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9331)) stack

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
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure s'

private def addrShiftRHashModGasProbeInstr : Instr :=
  mkAddrShiftRHashModInstr 7

private def addrShiftRHashModSetGasExact : Int :=
  computeExactGasBudget addrShiftRHashModGasProbeInstr

private def addrShiftRHashModSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne addrShiftRHashModGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def smallSignedPool : Array Int :=
  #[-17, -13, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 13, 17]

private def pickIntFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNatFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickNatFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 1 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def genAddrShiftRHashModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/boundary" shift #[.num x, .num w], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/random" shift #[.num x, .num w], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/x-boundary" shift #[.num x, .num w], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/w-boundary" shift #[.num x, .num w], r4)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/w-zero" shift #[.num x, .num 0], r3)
    else if shape = 5 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/x-zero" shift #[.num 0, .num w], r3)
    else if shape = 6 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty" shift #[], r2)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/one-item" shift #[intV x], r3)
    else if shape = 8 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type-single-non-int"
        shift #[.null], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (wLike, r4) := pickNonInt r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/w-top-non-int" shift #[intV x, wLike], r4)
    else if shape = 10 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (xLike, r4) := pickNonInt r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/x-second-non-int" shift #[xLike, intV w], r4)
    else if shape = 11 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/both-non-int-w-first"
        shift #[.null, .cell Cell.empty], r2)
    else if shape = 12 then
      let (shift, r2) := randNat rng1 1 4
      let (x, r3) := pickIntFromPool smallSignedPool r2
      let (w, r4) := pickIntFromPool smallSignedPool r3
      let (pickNull, r5) := randBool r4
      let below : Value := if pickNull then .null else .cell Cell.empty
      (mkShiftCase s!"/fuzz/shape-{shape}/pop-order/lower-preserved"
        shift #[below, intV x, intV w], r5)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/w-via-program" shift #[.num x, .nan], r3)
    else if shape = 14 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/x-via-program" shift #[.nan, .num w], r3)
    else if shape = 15 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/both-via-program" shift #[.nan, .nan], r2)
    else if shape = 16 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        shift #[.num xOut, .num w], r4)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        shift #[.num x, .num wOut], r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/boundary/shift1" 1 #[.num x, .num w], r3)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/boundary/shift256" 256 #[.num x, .num w], r3)
    else if shape = 20 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/boundary/max-plus-min"
        1 #[.num maxInt257, .num minInt257], rng1)
    else
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nonexact/small"
        2 #[.num 5, .num 2], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := addrShiftRHashModId
  unit := #[
    { name := "/unit/direct/exact-sum-cases-and-pop-order"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (21, 11, 1, 16, 0),
            (-21, 5, 2, -4, 0),
            (40, 24, 3, 8, 0),
            (0, 0, 256, 0, 0),
            (maxInt257, -1, 1, (pow2 255) - 1, 0),
            (minInt257, 0, 1, -(pow2 255), 0)
          ]
        for check in checks do
          match check with
          | (x, w, shift, q, r) =>
              expectOkStack s!"/unit/direct/x={x}/w={w}/z={shift}"
                (runAddrShiftRHashModDirect shift #[intV x, intV w]) #[intV q, intV r]
        expectOkStack "/unit/pop-order/lower-null-preserved"
          (runAddrShiftRHashModDirect 1 #[.null, intV 21, intV 11]) #[.null, intV 16, intV 0]
        expectOkStack "/unit/pop-order/lower-cell-preserved"
          (runAddrShiftRHashModDirect 2 #[.cell Cell.empty, intV (-21), intV 5])
          #[.cell Cell.empty, intV (-4), intV 0] }
    ,
    { name := "/unit/error/underflow-type-and-pop-order"
      run := do
        expectErr "/unit/error/underflow/empty"
          (runAddrShiftRHashModDirect 1 #[]) .stkUnd
        expectErr "/unit/error/underflow/one-item"
          (runAddrShiftRHashModDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-single-non-int"
          (runAddrShiftRHashModDirect 1 #[.null]) .stkUnd
        expectErr "/unit/error/type/w-top-null"
          (runAddrShiftRHashModDirect 1 #[intV 7, .null]) .typeChk
        expectErr "/unit/error/type/w-top-cell"
          (runAddrShiftRHashModDirect 1 #[intV 7, .cell Cell.empty]) .typeChk
        expectErr "/unit/error/type/x-second-null"
          (runAddrShiftRHashModDirect 1 #[.null, intV 7]) .typeChk
        expectErr "/unit/error-order/both-non-int-w-first"
          (runAddrShiftRHashModDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkAddrShiftRHashModInstr 1
        let instr256 := mkAddrShiftRHashModInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/addrshiftr-hash-mod-z1" s0 instr1 24
        let s2 ← expectDecodeStep "decode/addrshiftr-hash-mod-z256" s1 instr256 24
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/opcode/encode-invalid-immediate-range"
      run := do
        let invalidLow := mkAddrShiftRHashModInstr 0
        let invalidHigh := mkAddrShiftRHashModInstr 257
        match assembleCp0 [invalidLow] with
        | .ok _ =>
            throw (IO.userError "/unit/encode/range/shift0: expected rangeChk, got ok")
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"/unit/encode/range/shift0: expected rangeChk, got {e}")
        match assembleCp0 [invalidHigh] with
        | .ok _ =>
            throw (IO.userError "/unit/encode/range/shift257: expected rangeChk, got ok")
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"/unit/encode/range/shift257: expected rangeChk, got {e}") }
    ,
    { name := "/unit/dispatch/non-addrshiftr-hash-mod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runAddrShiftRHashModDispatchFallback #[]) #[intV 9331] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/exact/shift1-pos" 1 #[.num 21, .num 11],
    mkShiftInputCase "/ok/exact/shift2-neg" 2 #[.num (-21), .num 5],
    mkShiftInputCase "/ok/exact/shift3-pos" 3 #[.num 40, .num 24],
    mkShiftInputCase "/ok/exact/shift256-zero" 256 #[.num 0, .num 0],
    mkShiftInputCase "/ok/exact/shift1-max-minus-one" 1 #[.num maxInt257, .num (-1)],
    mkShiftInputCase "/ok/exact/shift1-min" 1 #[.num minInt257, .num 0],
    mkShiftInputCase "/ok/nonexact/shift1-pos" 1 #[.num 7, .num 0],
    mkShiftInputCase "/ok/nonexact/shift1-neg" 1 #[.num (-7), .num 0],
    mkShiftInputCase "/ok/nonexact/shift2-pos" 2 #[.num 5, .num 2],
    mkShiftInputCase "/ok/nonexact/shift2-neg" 2 #[.num (-5), .num (-2)],
    mkShiftInputCase "/ok/nonexact/shift256-max-plus-max" 256 #[.num maxInt257, .num maxInt257],
    mkShiftInputCase "/ok/nonexact/shift256-min-plus-min" 256 #[.num minInt257, .num minInt257],
    mkShiftInputCase "/ok/boundary/shift1-max-plus-min" 1 #[.num maxInt257, .num minInt257],
    mkShiftInputCase "/ok/boundary/shift1-max-plus-max" 1 #[.num maxInt257, .num maxInt257],
    mkShiftInputCase "/ok/boundary/shift1-min-plus-min" 1 #[.num minInt257, .num minInt257],
    mkShiftInputCase "/ok/boundary/shift256-one-plus-zero" 256 #[.num 1, .num 0],
    mkShiftCase "/ok/pop-order/lower-null-preserved" 1 #[.null, intV 21, intV 11],
    mkShiftCase "/ok/pop-order/lower-cell-preserved" 2 #[.cell Cell.empty, intV (-21), intV 5],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/underflow/one-item" 1 #[intV 1],
    mkShiftCase "/error-order/underflow-before-type-single-non-int" 1 #[.null],
    mkShiftCase "/type/w-top-null" 1 #[intV 7, .null],
    mkShiftCase "/type/w-top-cell" 1 #[intV 7, .cell Cell.empty],
    mkShiftCase "/type/x-second-null" 1 #[.null, intV 7],
    mkShiftCase "/error-order/both-non-int-w-first" 1 #[.null, .cell Cell.empty],
    mkShiftInputCase "/intov/nan-w-via-program" 1 #[.num 7, .nan],
    mkShiftInputCase "/intov/nan-x-via-program" 1 #[.nan, .num 7],
    mkShiftInputCase "/intov/nan-both-via-program" 1 #[.nan, .nan],
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op"
      1 #[.num (maxInt257 + 1), .num 7],
    mkShiftInputCase "/error-order/pushint-overflow-w-before-op"
      1 #[.num 7, .num (maxInt257 + 1)],
    mkShiftInputCase "/error-order/pushint-overflow-both-before-op"
      1 #[.num (maxInt257 + 1), .num (minInt257 - 1)],
    mkCase "/gas/exact-cost-succeeds" #[intV 21, intV 11]
      #[.pushInt (.num addrShiftRHashModSetGasExact), .tonEnvOp .setGasLimit, addrShiftRHashModGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 21, intV 11]
      #[.pushInt (.num addrShiftRHashModSetGasExactMinusOne), .tonEnvOp .setGasLimit, addrShiftRHashModGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020841
      count := 700
      gen := genAddrShiftRHashModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.ADDRSHIFTR_HASH_MOD
