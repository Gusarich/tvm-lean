import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFT_HASH_DIVMOD

/-
LSHIFT#DIVMOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shlDivMod 3 (-1) false false (some z))` path)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate `0xa9dc..0xa9de ++ (z-1)` encoding)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeInstrCp0`, `0xa9dc..0xa9de` decode to hash-immediate `.shlDivMod`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`d=3`, `roundMode=-1`, `add=false`, `quiet=false`, `zOpt=some z` specialization):
- Lean: 9 branch sites / 11 terminal outcomes
  (dispatch/fallback; underflow gate; immediate-shift range gate; `y` pop type;
   `x` pop type; numeric-vs-NaN split; divisor-zero split; floor division path;
   dual push funnel fit-vs-`intOv`).
- C++: 9 branch sites / 11 aligned terminal outcomes
  (`check_underflow(2)`; immediate-shift decode/range guard; `pop_int` for divisor;
   `pop_int` for numerator; invalid-input funnel; divisor-zero split; floor path;
   quotient/remainder push funnel fit-vs-`int_ov`).

Key risk areas covered:
- hash-immediate shift must not be popped from stack (only divisor then numerator pop);
- floor quotient/remainder invariants across sign mixes and boundary shifts (`1`, `255`, `256`);
- strict error order: underflow before type checks, and divisor (`y`) type before numerator (`x`);
- non-quiet `intOv` funnels for divisor-zero, NaN operands, and signed-257 overflow;
- oracle serialization constraints: NaN / out-of-range integers injected via `PUSHINT` prelude only;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; LSHIFT#DIVMOD`.
-/

private def lshiftHashDivmodId : InstrId := { name := "LSHIFT#DIVMOD" }

private def lshiftHashDivmodInstr (shift : Nat) : Instr :=
  .arithExt (.shlDivMod 3 (-1) false false (some shift))

private def lshiftHashDivmodInstrDefault : Instr :=
  lshiftHashDivmodInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftHashDivmodInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftHashDivmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkShiftCase
    (name : String)
    (x y : Int)
    (shift : Nat)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name #[intV x, intV y] #[lshiftHashDivmodInstr shift] gasLimits fuel

private def mkInputCase
    (name : String)
    (x y : IntVal)
    (shift : Nat := 1)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram #[x, y]
  mkCase name stack (programPrefix.push (lshiftHashDivmodInstr shift)) gasLimits fuel

private def runLshiftHashDivmodDirect (shift : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (lshiftHashDivmodInstr shift) stack

private def runLshiftHashDivmodDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9364)) stack

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

private def lshiftHashDivmodSetGasExact : Int :=
  computeExactGasBudget lshiftHashDivmodInstrDefault

private def lshiftHashDivmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftHashDivmodInstrDefault

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftOverflowPool : Array Nat :=
  #[1, 2, 3, 7, 8, 16, 64, 128, 255, 256]

private def smallDivisorPool : Array Int :=
  #[-7, -5, -3, -2, -1, 1, 2, 3, 5, 7]

private def smallNumeratorPool : Array Int :=
  #[-17, -13, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 13, 17]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickFromNatPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickValidShift (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickFromNatPool shiftBoundaryPool rng1
  else
    randNat rng1 1 256

private def pickOverflowShift (rng : StdGen) : Nat × StdGen :=
  pickFromNatPool shiftOverflowPool rng

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (n, rng1) := pickSigned257ish rng0
  (if n = 0 then 1 else n, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  (if pickCell then .cell Cell.empty else .null, rng')

private def classifyLshiftHashDivmod (x y : Int) (shift : Nat) : String :=
  if y = 0 then
    "intov-divzero"
  else
    let tmp : Int := x * intPow2 shift
    let (q, r) := divModRound tmp y (-1)
    if !intFitsSigned257 q || !intFitsSigned257 r then
      "intov-overflow"
    else if r = 0 then
      "ok-exact"
    else
      "ok-inexact"

private def mkFiniteFuzzCase (shape : Nat) (x y : Int) (shift : Nat) : OracleCase :=
  let kind := classifyLshiftHashDivmod x y shift
  mkShiftCase s!"/fuzz/shape-{shape}/{kind}" x y shift

private def genLshiftHashDivmodFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickFromNatPool shiftBoundaryPool r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickValidShift r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 2 then
      let (x, r2) := pickFromIntPool smallNumeratorPool rng1
      let (y, r3) := pickFromIntPool smallDivisorPool r2
      let (shift, r4) := pickFromNatPool shiftBoundaryPool r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkShiftCase s!"/fuzz/shape-{shape}/intov-divzero" x 0 shift, r3)
    else if shape = 4 then
      let (shift, r2) := pickOverflowShift rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/intov-overflow-max" maxInt257 1 shift, r2)
    else if shape = 5 then
      let (shift, r2) := pickOverflowShift rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/intov-overflow-min" minInt257 1 shift, r2)
    else if shape = 6 then
      (mkCase s!"/fuzz/shape-{shape}/underflow-empty" #[], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow-one-int" #[intV x], r2)
    else if shape = 8 then
      let (v, r2) := pickNonInt rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow-one-non-int" #[v], r2)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (yLike, r3) := pickNonInt r2
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-first"
        #[intV x, yLike] #[lshiftHashDivmodInstrDefault], r3)
    else if shape = 10 then
      let (y, r2) := pickNonZeroInt rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-second"
        #[xLike, intV y] #[lshiftHashDivmodInstrDefault], r3)
    else if shape = 11 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-when-both-non-int"
        #[.null, .cell Cell.empty] #[lshiftHashDivmodInstrDefault], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/pop-order/immediate-does-not-pop-third-item"
        #[intV 42, intV x, intV y] #[lshiftHashDivmodInstr shift], r4)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkInputCase s!"/fuzz/shape-{shape}/intov-nan-divisor-via-program"
        (.num x) .nan shift, r3)
    else if shape = 14 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickValidShift r2
      (mkInputCase s!"/fuzz/shape-{shape}/intov-nan-numerator-via-program"
        .nan (.num y) shift, r3)
    else if shape = 15 then
      let (x, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickValidShift r2
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        (.num x) (.num 3) shift, r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickValidShift r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        (.num x) (.num y) shift, r4)
    else if shape = 17 then
      let (x, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickValidShift r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-both-before-op"
        (.num x) (.num y) shift, r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkShiftCase s!"/fuzz/shape-{shape}/boundary/shift-256" x y 256, r3)
    else if shape = 19 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickFromIntPool smallDivisorPool r2
      (mkShiftCase s!"/fuzz/shape-{shape}/boundary/shift-1" x y 1, r3)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/exact/div-by-one" x 1 1, r2)
    else
      (mkCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type"
        #[.null] #[lshiftHashDivmodInstrDefault], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftHashDivmodId
  unit := #[
    { name := "/unit/direct/floor-sign-shift-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (13, 3, 2, 17, 1),
            (-13, 3, 1, -9, 1),
            (13, -3, 2, -18, -2),
            (-13, -3, 2, 17, -1),
            (7, 3, 1, 4, 2),
            (-7, 3, 1, -5, 1),
            (7, -3, 1, -5, -1),
            (-7, -3, 1, 4, -2),
            (1, 5, 8, 51, 1),
            (0, 3, 256, 0, 0),
            (maxInt257, 2, 1, maxInt257, 0),
            (minInt257, 2, 1, minInt257, 0),
            (minInt257 + 1, 2, 1, minInt257 + 1, 0)
          ]
        for c in checks do
          match c with
          | (x, y, shift, q, r) =>
              expectOkStack s!"/unit/direct/x={x}/y={y}/shift={shift}"
                (runLshiftHashDivmodDirect shift #[intV x, intV y]) #[intV q, intV r] }
    ,
    { name := "/unit/direct/hash-immediate-shift-does-not-pop-third-item"
      run := do
        expectOkStack "/unit/pop-order/residue-preserved"
          (runLshiftHashDivmodDirect 1 #[intV 99, intV 7, intV 3]) #[intV 99, intV 4, intV 2] }
    ,
    { name := "/unit/error/intov-funnels-divzero-and-overflow"
      run := do
        expectErr "/unit/intov/divzero/nonzero-over-zero"
          (runLshiftHashDivmodDirect 1 #[intV 7, intV 0]) .intOv
        expectErr "/unit/intov/divzero/zero-over-zero"
          (runLshiftHashDivmodDirect 256 #[intV 0, intV 0]) .intOv
        expectErr "/unit/intov/overflow/max-shift1-div1"
          (runLshiftHashDivmodDirect 1 #[intV maxInt257, intV 1]) .intOv
        expectErr "/unit/intov/overflow/min-shift1-div1"
          (runLshiftHashDivmodDirect 1 #[intV minInt257, intV 1]) .intOv }
    ,
    { name := "/unit/error/underflow-and-pop-order"
      run := do
        expectErr "/unit/underflow/empty" (runLshiftHashDivmodDirect 1 #[]) .stkUnd
        expectErr "/unit/underflow/one-int" (runLshiftHashDivmodDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/underflow/one-non-int" (runLshiftHashDivmodDirect 1 #[.null]) .stkUnd
        expectErr "/unit/type/pop-y-first-null"
          (runLshiftHashDivmodDirect 1 #[intV 1, .null]) .typeChk
        expectErr "/unit/type/pop-y-first-cell"
          (runLshiftHashDivmodDirect 1 #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "/unit/type/pop-x-second-null"
          (runLshiftHashDivmodDirect 1 #[.null, intV 1]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-when-both-non-int"
          (runLshiftHashDivmodDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/error/invalid-immediate-shift-range-before-pop"
      run := do
        let invalidLow : Instr := .arithExt (.shlDivMod 3 (-1) false false (some 0))
        let invalidHigh : Instr := .arithExt (.shlDivMod 3 (-1) false false (some 257))
        expectErr "/unit/error-order/underflow-before-range-invalid-immediate"
          (runHandlerDirect execInstrArithExt invalidLow #[]) .stkUnd
        expectErr "/unit/error-order/range-before-y-type-invalid-immediate-low"
          (runHandlerDirect execInstrArithExt invalidLow #[intV 7, .null]) .rangeChk
        expectErr "/unit/error-order/range-before-x-type-invalid-immediate-high"
          (runHandlerDirect execInstrArithExt invalidHigh #[.null, intV 7]) .rangeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let i17 := lshiftHashDivmodInstr 17
        let program : Array Instr := #[i17, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/lshift-hash-divmod" s0 i17 24
        let s2 ← expectDecodeStep "/unit/decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-shldivmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runLshiftHashDivmodDispatchFallback #[]) #[intV 9364] }
  ]
  oracle := #[
    mkShiftCase "/ok/floor/sign/pos-pos-shift1" 7 3 1,
    mkShiftCase "/ok/floor/sign/neg-pos-shift1" (-7) 3 1,
    mkShiftCase "/ok/floor/sign/pos-neg-shift1" 7 (-3) 1,
    mkShiftCase "/ok/floor/sign/neg-neg-shift1" (-7) (-3) 1,
    mkShiftCase "/ok/floor/exact/divisible-shift2" 9 3 2,
    mkShiftCase "/ok/floor/inexact/shift2-small" 1 3 2,
    mkShiftCase "/ok/floor/zero-numerator-shift256" 0 5 256,
    mkShiftCase "/ok/boundary/max-shift1-div2" maxInt257 2 1,
    mkShiftCase "/ok/boundary/min-shift1-div2" minInt257 2 1,
    mkShiftCase "/ok/boundary/min-plus-one-shift1-div2" (minInt257 + 1) 2 1,
    mkShiftCase "/ok/boundary/one-shift256-div-max" 1 maxInt257 256,
    mkShiftCase "/ok/boundary/negone-shift256-div-max" (-1) maxInt257 256,
    mkCase "/ok/pop-order/hash-immediate-does-not-pop-third-item"
      #[intV 99, intV 7, intV 3]
      #[lshiftHashDivmodInstr 1],
    mkShiftCase "/intov/divzero/nonzero-over-zero" 7 0 1,
    mkShiftCase "/intov/divzero/zero-over-zero" 0 0 256,
    mkShiftCase "/intov/overflow/max-shift1-div1" maxInt257 1 1,
    mkShiftCase "/intov/overflow/min-shift1-div1" minInt257 1 1,
    mkCase "/underflow/empty-stack" #[] #[lshiftHashDivmodInstrDefault],
    mkCase "/underflow/one-int" #[intV 1] #[lshiftHashDivmodInstrDefault],
    mkCase "/underflow/one-non-int-underflow-before-type" #[.null] #[lshiftHashDivmodInstrDefault],
    mkCase "/type/pop-y-first-null" #[intV 1, .null] #[lshiftHashDivmodInstrDefault],
    mkCase "/type/pop-y-first-cell" #[intV 1, .cell Cell.empty] #[lshiftHashDivmodInstrDefault],
    mkCase "/type/pop-x-second-null" #[.null, intV 1] #[lshiftHashDivmodInstrDefault],
    mkCase "/error-order/pop-y-before-x-when-both-non-int" #[.null, .cell Cell.empty] #[lshiftHashDivmodInstrDefault],
    mkInputCase "/intov/nan-divisor-via-program" (.num 7) .nan 1,
    mkInputCase "/intov/nan-numerator-via-program" .nan (.num 3) 1,
    mkInputCase "/error-order/pushint-overflow-x-before-op" (.num (maxInt257 + 1)) (.num 3) 1,
    mkInputCase "/error-order/pushint-overflow-y-before-op" (.num 7) (.num (maxInt257 + 1)) 1,
    mkInputCase "/error-order/pushint-overflow-both-before-op"
      (.num (maxInt257 + 1)) (.num (minInt257 - 1)) 1,
    mkCase "/gas/exact-cost-succeeds" #[intV 13, intV 3]
      #[.pushInt (.num lshiftHashDivmodSetGasExact), .tonEnvOp .setGasLimit, lshiftHashDivmodInstrDefault],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 13, intV 3]
      #[.pushInt (.num lshiftHashDivmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftHashDivmodInstrDefault]
  ]
  fuzz := #[
    { seed := 2026020866
      count := 700
      gen := genLshiftHashDivmodFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFT_HASH_DIVMOD
