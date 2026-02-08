import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MODPOW2C_HASH

/-
MODPOW2C# branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false false 2 1 false (some z)` specialization)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`modPow2Round` ceil-mode remainder semantics)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash immediate `0xa938..0xa93a`, `z ∈ [1, 256]`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, hash decode family `0xa938..0xa93a`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, opcode wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::mod_pow2`, ceil rounding)

Branch/terminal counts used for this suite (`mul=false`, `add=false`, `d=2`,
`roundMode=1`, `quiet=false`, `zOpt=some`):
- Lean specialization: 7 branch sites / 9 terminal outcomes
  (dispatch/fallback; arity precheck; x pop type/success; finite-vs-NaN split;
   non-quiet push success-vs-`intOv`; hash-immediate encode/decode range gate).
- C++ specialization: 6 branch sites / 9 aligned terminal outcomes
  (invalid-op guard; underflow check; `pop_int` type path; `y==0` override
   branch unreachable via valid decode; finite-vs-invalid integer path;
   non-quiet `push_int_quiet` success-vs-`int_ov`).

Lean/C++ outcome mapping covered:
- `stkUnd`: pre-pop underflow for one-arg hash form;
- `typeChk`: only `x` is popped at execution time (no runtime shift pop);
- finite success: ceil-mod remainder `r = x - ceil(x / 2^z) * 2^z`;
- `intOv`: non-quiet NaN funnel (program-injected) and pre-op `PUSHINT` overflow;
- pop-order: top `x` consumed, below-stack values preserved on success;
- serialization: NaN/out-of-range oracle inputs are injected through program prelude only.

Key risk areas covered:
- immediate boundary correctness (`z = 1`, `z = 256`) and decode stability;
- sign/tie behavior of ceil remainder on small and 257-bit boundaries;
- single-pop semantics vs legacy runtime-shift mental model;
- error-order between prelude failures and instruction execution;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; MODPOW2C#`.
-/

private def modpow2cHashId : InstrId := { name := "MODPOW2C#" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkModpow2cHashInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod false false 2 1 false (some shift))

private def modpow2cHashInstrDefault : Instr :=
  mkModpow2cHashInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[modpow2cHashInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := modpow2cHashId
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
  mkCase name stack #[mkModpow2cHashInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkModpow2cHashInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix.push instr) gasLimits fuel

private def runModpow2cHashDirect (shift : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkModpow2cHashInstr shift) stack

private def runModpow2cHashDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9237)) stack

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

private def modpow2cHashGasProbeInstr : Instr :=
  mkModpow2cHashInstr 7

private def modpow2cHashSetGasExact : Int :=
  computeExactGasBudget modpow2cHashGasProbeInstr

private def modpow2cHashSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne modpow2cHashGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def ceilFocusXPool : Array Int :=
  #[-13, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 13, 42, -42]

private def pickNatFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickIntFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickNatFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  ((if pickNull then .null else .cell Cell.empty), rng')

private def genModpow2cHashFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/boundary" shift #[intV x], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/random" shift #[intV x], r3)
    else if shape = 2 then
      let (x, r2) := pickIntFromPool ceilFocusXPool rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/ceil-focus" shift #[intV x], r3)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/shift256" 256 #[intV x], r2)
    else if shape = 4 then
      let (pickMin, r2) := randBool rng1
      let x : Int := if pickMin then minInt257 else maxInt257
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/extreme-x" shift #[intV x], r3)
    else if shape = 5 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty" shift #[], r2)
    else if shape = 6 then
      let (shift, r2) := pickShiftBoundary rng1
      let (xLike, r3) := pickNonInt r2
      (mkShiftCase s!"/fuzz/shape-{shape}/type/x-non-int" shift #[xLike], r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := randNat r2 1 4
      let (below, r4) := pickNonInt r3
      (mkShiftCase s!"/fuzz/shape-{shape}/pop-order/below-preserved" shift #[below, intV x], r4)
    else if shape = 8 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/pop-x-first-before-below-non-int"
        shift #[.null, .cell Cell.empty], r2)
    else if shape = 9 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/x-via-program" shift #[.nan], r2)
    else if shape = 10 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op"
        shift #[.num xo], r3)
    else if shape = 11 then
      let (xo, r2) := pickInt257OutOfRange rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-shift256"
        256 #[.num xo], r2)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-prelude-before-op-pop"
        #[.null, intV x]
        #[.pushInt (.num (maxInt257 + 1)), mkModpow2cHashInstr 1], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/shift1" 1 #[intV x], r2)
    else if shape = 14 then
      let (x, r2) := pickInt257Boundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/shift255" 255 #[intV x], r2)
    else
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty-alt" shift #[], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := modpow2cHashId
  unit := #[
    { name := "/unit/direct/ceil-mod-sign-and-tie-invariants"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (7, 1, -1),
            (7, 2, -1),
            (9, 2, -3),
            (-7, 1, -1),
            (-7, 2, -3),
            (-9, 2, -1),
            (1, 1, -1),
            (-1, 1, -1),
            (42, 1, 0),
            (-42, 1, 0),
            (5, 3, -3),
            (-5, 3, -5)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"/unit/direct/x={x}/z={shift}"
            (runModpow2cHashDirect shift #[intV x]) #[intV expected] }
    ,
    { name := "/unit/direct/boundary-shifts-and-pop-order"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (maxInt257, 1, -1),
            (minInt257, 1, 0),
            (maxInt257, 256, -1),
            (maxInt257 - 1, 256, -2),
            (minInt257, 256, 0),
            (minInt257 + 1, 256, minInt257 + 1),
            (1, 256, minInt257 + 1),
            (-1, 256, -1)
          ]
        for c in checks do
          let x := c.1
          let shift := c.2.1
          let expected := c.2.2
          expectOkStack s!"/unit/boundary/x={x}/z={shift}"
            (runModpow2cHashDirect shift #[intV x]) #[intV expected]
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runModpow2cHashDirect 1 #[.null, intV 7]) #[.null, intV (-1)]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runModpow2cHashDirect 256 #[.cell Cell.empty, intV (-1)])
          #[.cell Cell.empty, intV (-1)] }
    ,
    { name := "/unit/error/underflow-type-and-pop-ordering"
      run := do
        expectErr "/unit/underflow/empty-stack"
          (runModpow2cHashDirect 1 #[]) .stkUnd
        expectErr "/unit/type/pop-x-null"
          (runModpow2cHashDirect 1 #[.null]) .typeChk
        expectErr "/unit/type/pop-x-cell"
          (runModpow2cHashDirect 256 #[.cell Cell.empty]) .typeChk
        expectErr "/unit/error-order/pop-x-first-before-below-non-int"
          (runModpow2cHashDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkModpow2cHashInstr 1
        let instr256 := mkModpow2cHashInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/decode/assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/modpow2c-hash-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/modpow2c-hash-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/opcode/encode-immediate-range-gate"
      run := do
        let bad0 := assembleCp0 [mkModpow2cHashInstr 0]
        match bad0 with
        | .ok _ =>
            throw (IO.userError "/unit/encode/range/shift0: expected rangeChk, got success")
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"/unit/encode/range/shift0: expected rangeChk, got {e}")
        let bad257 := assembleCp0 [mkModpow2cHashInstr 257]
        match bad257 with
        | .ok _ =>
            throw (IO.userError "/unit/encode/range/shift257: expected rangeChk, got success")
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"/unit/encode/range/shift257: expected rangeChk, got {e}") }
    ,
    { name := "/unit/dispatch/non-modpow2c-hash-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runModpow2cHashDispatchFallback #[]) #[intV 9237] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/ceil/pos-shift1" 1 #[.num 7],
    mkShiftInputCase "/ok/ceil/neg-shift1" 1 #[.num (-7)],
    mkShiftInputCase "/ok/ceil/tie-pos-half" 1 #[.num 1],
    mkShiftInputCase "/ok/ceil/tie-neg-half" 1 #[.num (-1)],
    mkShiftInputCase "/ok/ceil/exact-pos" 1 #[.num 42],
    mkShiftInputCase "/ok/ceil/exact-neg" 1 #[.num (-42)],
    mkShiftInputCase "/ok/ceil/pos-shift2" 2 #[.num 7],
    mkShiftInputCase "/ok/ceil/neg-shift2" 2 #[.num (-7)],
    mkShiftInputCase "/ok/ceil/pos-shift3" 3 #[.num 5],
    mkShiftInputCase "/ok/ceil/neg-shift3" 3 #[.num (-5)],
    mkShiftInputCase "/ok/boundary/max-shift1" 1 #[.num maxInt257],
    mkShiftInputCase "/ok/boundary/min-shift1" 1 #[.num minInt257],
    mkShiftInputCase "/ok/boundary/max-shift256" 256 #[.num maxInt257],
    mkShiftInputCase "/ok/boundary/max-minus-one-shift256" 256 #[.num (maxInt257 - 1)],
    mkShiftInputCase "/ok/boundary/min-shift256" 256 #[.num minInt257],
    mkShiftInputCase "/ok/boundary/min-plus-one-shift256" 256 #[.num (minInt257 + 1)],
    mkShiftInputCase "/ok/boundary/one-shift256" 256 #[.num 1],
    mkShiftInputCase "/ok/boundary/minus-one-shift256" 256 #[.num (-1)],
    mkShiftCase "/ok/pop-order/below-null-preserved" 1 #[.null, intV 7],
    mkShiftCase "/ok/pop-order/below-cell-preserved" 256 #[.cell Cell.empty, intV (-1)],
    mkShiftCase "/underflow/empty-stack-shift1" 1 #[],
    mkShiftCase "/underflow/empty-stack-shift256" 256 #[],
    mkShiftCase "/type/pop-x-null-shift1" 1 #[.null],
    mkShiftCase "/type/pop-x-cell-shift256" 256 #[.cell Cell.empty],
    mkShiftCase "/error-order/pop-x-first-before-below-non-int" 1 #[.null, .cell Cell.empty],
    mkShiftInputCase "/nan/x-via-program-shift3" 3 #[.nan],
    mkShiftInputCase "/error-order/pushint-overflow-x-high-before-op" 3 #[.num (maxInt257 + 1)],
    mkShiftInputCase "/error-order/pushint-overflow-x-low-before-op" 256 #[.num (minInt257 - 1)],
    mkCase "/error-order/pushint-overflow-prelude-before-op-pop"
      #[.null, intV 17] #[.pushInt (.num (maxInt257 + 1)), mkModpow2cHashInstr 1],
    mkCase "/gas/exact-cost-succeeds" #[intV 37]
      #[.pushInt (.num modpow2cHashSetGasExact), .tonEnvOp .setGasLimit, modpow2cHashGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 37]
      #[.pushInt (.num modpow2cHashSetGasExactMinusOne), .tonEnvOp .setGasLimit, modpow2cHashGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020815
      count := 700
      gen := genModpow2cHashFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MODPOW2C_HASH
