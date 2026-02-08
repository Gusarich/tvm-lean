import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.ADDRSHIFT_HASH_MOD

/-
ADDRSHIFT#MOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false true 3 (-1) false (some z)` specialization)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate SHR/MOD family `0xa930..0xa932`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, 24-bit hash-immediate decode path)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, stack underflow/type behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`mul=false`, `add=true`, `d=3`, `roundMode=-1`, `quiet=false`, `zOpt=some z`):
- Lean specialization: 7 branch sites / 10 terminal outcomes
  (dispatch/fallback; arity gate; `w` then `x` pop/type ordering; numeric-vs-NaN split;
   fixed round-mode validation; fixed `d=3` dual-push non-quiet funnel).
- C++ specialization: 6 branch sites / 10 aligned terminal outcomes
  (underflow gate; ordered `pop_int` for `w` then `x`; numeric-vs-invalid split;
   add+rshift/modpow2 floor path; non-quiet push funnel).

Key risk areas covered:
- hash-immediate behavior (`z` fixed by opcode, never popped from stack);
- explicit pop/error ordering (`stkUnd` before type; `w` before `x`);
- floor quotient/remainder invariants across sign mixes and boundary shifts;
- non-quiet `intOv` funnels for NaN operands;
- NaN and out-of-range integer injection in oracle/fuzz via prelude (`PUSHINT`) only;
- deterministic gas boundary with `computeExactGasBudget*` + `SETGASLIMIT`.
-/

private def addrshiftHashModId : InstrId := { name := "ADDRSHIFT#MOD" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkAddrShiftHashModInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod false true 3 (-1) false (some shift))

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := addrshiftHashModId
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
  mkCase name stack #[mkAddrShiftHashModInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkAddrShiftHashModInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (progPrefix.push instr) gasLimits fuel

private def runAddrShiftHashModDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkAddrShiftHashModInstr shift) stack

private def runAddrShiftHashModDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 8751)) stack

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

private def addrshiftHashModGasProbeInstr : Instr :=
  mkAddrShiftHashModInstr 7

private def addrshiftHashModSetGasExact : Int :=
  computeExactGasBudget addrshiftHashModGasProbeInstr

private def addrshiftHashModSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne addrshiftHashModGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def smallSignedPool : Array Int :=
  #[-33, -17, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 17, 33]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def pickIntFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  (if pickNull then .null else .cell Cell.empty, rng')

private def classifyAddrShiftHashMod (x w : Int) (shift : Nat) : String :=
  let tmp : Int := x + w
  let r := modPow2Round tmp shift (-1)
  if r = 0 then "ok-exact" else "ok-inexact"

private def genAddrShiftHashModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyAddrShiftHashMod x w shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-boundary" shift #[intV x, intV w], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyAddrShiftHashMod x w shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/signed-signed" shift #[intV x, intV w], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyAddrShiftHashMod x w shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/x-boundary" shift #[intV x, intV w], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftInRange r3
      let kind := classifyAddrShiftHashMod x w shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/w-boundary" shift #[intV x, intV w], r4)
    else if shape = 4 then
      let (x, r2) := pickIntFromPool smallSignedPool rng1
      let (w, r3) := pickIntFromPool smallSignedPool r2
      let (shift, r4) := pickShiftBoundary r3
      let kind := classifyAddrShiftHashMod x w shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/small-signed" shift #[intV x, intV w], r4)
    else if shape = 5 then
      let (x0, r2) := pickInt257Boundary rng1
      let x := if x0 = minInt257 then minInt257 + 1 else x0
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyAddrShiftHashMod x (-x) shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/canceling-addend" shift #[intV x, intV (-x)], r3)
    else if shape = 6 then
      (mkShiftCase s!"/fuzz/shape-{shape}/ok-exact/max-plus-max-shift256"
        256 #[intV maxInt257, intV maxInt257], rng1)
    else if shape = 7 then
      (mkShiftCase s!"/fuzz/shape-{shape}/ok-exact/min-plus-min-shift256"
        256 #[intV minInt257, intV minInt257], rng1)
    else if shape = 8 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty" shift #[], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/one-int" shift #[intV x], r3)
    else if shape = 10 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type-single-non-int"
        shift #[.null], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (wBad, r3) := pickNonInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/pop-w-first-non-int"
        shift #[intV x, wBad], r4)
    else if shape = 12 then
      let (w, r2) := pickSigned257ish rng1
      let (xBad, r3) := pickNonInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/pop-x-second-non-int"
        shift #[xBad, intV w], r4)
    else if shape = 13 then
      let (xBad, r2) := pickNonInt rng1
      let (wBad, r3) := pickNonInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/pop-w-before-x-when-both-non-int"
        shift #[xBad, wBad], r4)
    else if shape = 14 then
      let (x, r2) := pickIntFromPool smallSignedPool rng1
      let (w, r3) := pickIntFromPool smallSignedPool r2
      let (shift, r4) := pickShiftBoundary r3
      let (pickNull, r5) := randBool r4
      let below : Value := if pickNull then .null else .cell Cell.empty
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/pop-order/below-preserved"
        shift #[below, intV x, intV w], r5)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-w-via-program"
        shift #[.num x, .nan], r3)
    else if shape = 16 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program"
        shift #[.nan, .num w], r3)
    else if shape = 17 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        shift #[.num xOut, .num w], r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        shift #[.num x, .num wOut], r4)
    else if shape = 19 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-both-before-op"
        shift #[.num xOut, .num wOut], r4)
    else if shape = 20 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-both-via-program"
        shift #[.nan, .nan], r2)
    else
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/fallback" 1 #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := addrshiftHashModId
  unit := #[
    { name := "/unit/direct/floor-sign-shift-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (7, 5, 2, 3, 0),
            (-7, 1, 2, -2, 2),
            (7, -8, 2, -1, 3),
            (-7, -1, 2, -2, 0),
            (1, -2, 1, -1, 1),
            (-1, 2, 1, 0, 1),
            (9, -9, 5, 0, 0),
            (5, 3, 1, 4, 0),
            (-5, -3, 1, -4, 0),
            (maxInt257, maxInt257, 256, 1, (pow2 256) - 2),
            (minInt257, minInt257, 256, -2, 0),
            (minInt257, 1, 256, -1, 1),
            (maxInt257, -1, 256, 0, (pow2 256) - 2),
            (maxInt257, minInt257, 1, -1, 1)
          ]
        for c in checks do
          let x := c.1
          let w := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2.1
          let r := c.2.2.2.2
          expectOkStack s!"/unit/direct/x={x}/w={w}/z={shift}"
            (runAddrShiftHashModDirect shift #[intV x, intV w]) #[intV q, intV r] }
    ,
    { name := "/unit/direct/pop-order-and-below-stack-preservation"
      run := do
        expectOkStack "/unit/direct/pop-order/below-null-preserved"
          (runAddrShiftHashModDirect 3 #[.null, intV 13, intV 3])
          #[.null, intV 2, intV 0]
        expectOkStack "/unit/direct/pop-order/below-cell-preserved"
          (runAddrShiftHashModDirect 2 #[.cell Cell.empty, intV (-13), intV 3])
          #[.cell Cell.empty, intV (-3), intV 2] }
    ,
    { name := "/unit/error/underflow-type-and-pop-error-order"
      run := do
        expectErr "/unit/error/underflow/empty"
          (runAddrShiftHashModDirect 1 #[]) .stkUnd
        expectErr "/unit/error/underflow/one-int"
          (runAddrShiftHashModDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow-before-type/single-non-int"
          (runAddrShiftHashModDirect 1 #[.null]) .stkUnd
        expectErr "/unit/error/type/pop-w-first"
          (runAddrShiftHashModDirect 1 #[intV 1, .null]) .typeChk
        expectErr "/unit/error/type/pop-x-second"
          (runAddrShiftHashModDirect 1 #[.null, intV 1]) .typeChk
        expectErr "/unit/error/order/pop-w-before-x-when-both-non-int"
          (runAddrShiftHashModDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkAddrShiftHashModInstr 1
        let instr256 := mkAddrShiftHashModInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/addrshift-hash-mod-z1" s0 instr1 24
        let s2 ← expectDecodeStep "decode/addrshift-hash-mod-z256" s1 instr256 24
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-shrmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runAddrShiftHashModDispatchFallback #[]) #[intV 8751] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/floor/basic/pos-pos" 2 #[.num 7, .num 5],
    mkShiftInputCase "/ok/floor/basic/neg-pos" 2 #[.num (-7), .num 1],
    mkShiftInputCase "/ok/floor/basic/pos-neg" 2 #[.num 7, .num (-8)],
    mkShiftInputCase "/ok/floor/basic/neg-neg" 2 #[.num (-7), .num (-1)],
    mkShiftInputCase "/ok/floor/basic/shift1-mixed-a" 1 #[.num 1, .num (-2)],
    mkShiftInputCase "/ok/floor/basic/shift1-mixed-b" 1 #[.num (-1), .num 2],
    mkShiftInputCase "/ok/floor/basic/canceling-sum" 5 #[.num 9, .num (-9)],
    mkShiftInputCase "/ok/boundary/max-plus-max-shift256" 256 #[.num maxInt257, .num maxInt257],
    mkShiftInputCase "/ok/boundary/min-plus-min-shift256" 256 #[.num minInt257, .num minInt257],
    mkShiftInputCase "/ok/boundary/min-plus-one-shift256" 256 #[.num minInt257, .num 1],
    mkShiftInputCase "/ok/boundary/max-plus-negone-shift256" 256 #[.num maxInt257, .num (-1)],
    mkShiftInputCase "/ok/boundary/max-plus-min-shift1" 1 #[.num maxInt257, .num minInt257],
    mkShiftCase "/ok/pop-order/below-null-preserved" 3 #[.null, intV 13, intV 3],
    mkShiftCase "/ok/pop-order/below-cell-preserved" 2 #[.cell Cell.empty, intV (-13), intV 3],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/underflow/one-item" 1 #[intV 1],
    mkShiftCase "/error-order/underflow-before-type-single-non-int" 1 #[.null],
    mkShiftCase "/type/pop-w-first-null" 1 #[intV 1, .null],
    mkShiftCase "/type/pop-w-first-cell" 1 #[intV 1, .cell Cell.empty],
    mkShiftCase "/type/pop-x-second-null" 1 #[.null, intV 1],
    mkShiftCase "/type/pop-x-second-cell" 1 #[.cell Cell.empty, intV 1],
    mkShiftCase "/error-order/pop-w-before-x-when-both-non-int" 1 #[.null, .cell Cell.empty],
    mkShiftCase "/error-order/pop-w-before-x-when-both-cells" 1 #[.cell Cell.empty, .cell Cell.empty],
    mkShiftInputCase "/intov/nan-w-via-program" 4 #[.num 5, .nan],
    mkShiftInputCase "/intov/nan-x-via-program" 4 #[.nan, .num 5],
    mkShiftInputCase "/intov/nan-both-via-program" 4 #[.nan, .nan],
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op" 3 #[.num (maxInt257 + 1), .num 1],
    mkShiftInputCase "/error-order/pushint-overflow-w-before-op" 3 #[.num 7, .num (maxInt257 + 1)],
    mkShiftInputCase "/error-order/pushint-overflow-both-before-op" 3 #[.num (maxInt257 + 1), .num (minInt257 - 1)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num addrshiftHashModSetGasExact), .tonEnvOp .setGasLimit, addrshiftHashModGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num addrshiftHashModSetGasExactMinusOne), .tonEnvOp .setGasLimit, addrshiftHashModGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020815
      count := 700
      gen := genAddrShiftHashModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.ADDRSHIFT_HASH_MOD
