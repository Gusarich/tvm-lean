import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFT_HASH_DIV

/-
LSHIFT#DIV branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shlDivMod 1 (-1) false false (some z))` path)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate `0xa9d4..0xa9d6 ++ (z-1)` encoding)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeInstrCp0`, `0xa9d4..0xa9d6` decode to hash-immediate `.shlDivMod`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`d=1`, `roundMode=-1`, `add=false`, `quiet=false`, `zOpt=some z` specialization):
- Lean: 8 branch sites / 10 terminal outcomes
  (dispatch/fallback; underflow gate; immediate-shift range gate; `y` pop type;
   `x` pop type; numeric-vs-NaN split; divisor-zero split; non-quiet push fit-vs-`intOv`).
- C++: 8 branch sites / 10 aligned terminal outcomes
  (`check_underflow(2)`; immediate-shift decode/range guard; `pop_int` for divisor;
   `pop_int` for numerator; v13 invalid-input funnel; divisor-zero split;
   floor division path; `push_int_quiet` fit-vs-`int_ov`).

Key risk areas covered:
- hash-immediate shift must not be popped from stack (only divisor then numerator pop);
- floor rounding behavior over sign mixes and boundary shifts (`1`, `255`, `256`);
- strict error order: underflow before type checks, and divisor (`y`) type before numerator (`x`);
- non-quiet funnels (`intOv`) for divisor-zero, NaN operands, and signed-257 overflow;
- oracle serialization constraints: NaN / out-of-range integers injected via `PUSHINT` prelude only;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; LSHIFT#DIV`.
-/

private def lshiftHashDivId : InstrId := { name := "LSHIFT#DIV" }

private def lshiftHashDivInstr (shift : Nat) : Instr :=
  .arithExt (.shlDivMod 1 (-1) false false (some shift))

private def lshiftHashDivInstrDefault : Instr :=
  lshiftHashDivInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftHashDivInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftHashDivId
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
  mkCase name #[intV x, intV y] #[lshiftHashDivInstr shift] gasLimits fuel

private def mkInputCase
    (name : String)
    (x y : IntVal)
    (shift : Nat := 1)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram #[x, y]
  mkCase name stack (programPrefix.push (lshiftHashDivInstr shift)) gasLimits fuel

private def runLshiftHashDivDirect (shift : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (lshiftHashDivInstr shift) stack

private def runLshiftHashDivDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9304)) stack

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

private def lshiftHashDivSetGasExact : Int :=
  computeExactGasBudget lshiftHashDivInstrDefault

private def lshiftHashDivSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftHashDivInstrDefault

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

private def classifyLshiftHashDiv (x y : Int) (shift : Nat) : String :=
  if y = 0 then
    "intov-divzero"
  else
    let tmp : Int := x * intPow2 shift
    let (q, r) := divModRound tmp y (-1)
    if !intFitsSigned257 q then
      "intov-overflow"
    else if r = 0 then
      "ok-exact"
    else
      "ok-inexact"

private def mkFiniteFuzzCase (shape : Nat) (x y : Int) (shift : Nat) : OracleCase :=
  let kind := classifyLshiftHashDiv x y shift
  mkShiftCase s!"/fuzz/shape-{shape}/{kind}" x y shift

private def genLshiftHashDivFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
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
        #[intV x, yLike] #[lshiftHashDivInstrDefault], r3)
    else if shape = 10 then
      let (y, r2) := pickNonZeroInt rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-second"
        #[xLike, intV y] #[lshiftHashDivInstrDefault], r3)
    else if shape = 11 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-when-both-non-int"
        #[.null, .cell Cell.empty] #[lshiftHashDivInstrDefault], rng1)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/pop-order/immediate-does-not-pop-third-item"
        #[intV 42, intV x, intV y] #[lshiftHashDivInstr shift], r4)
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
      let (y, r2) := pickNonZeroInt rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type"
        y y 1 |> fun c => { c with initStack := #[.null] }, r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftHashDivId
  unit := #[
    { name := "/unit/direct/floor-sign-and-shift-invariants"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (7, 3, 1, 4),
            (-7, 3, 1, -5),
            (7, -3, 1, -5),
            (-7, -3, 1, 4),
            (1, 3, 2, 1),
            (-1, 3, 2, -2),
            (5, 2, 1, 5),
            (9, 3, 2, 12),
            (0, 5, 256, 0),
            (maxInt257, 2, 1, maxInt257),
            (minInt257, 2, 1, minInt257),
            (minInt257 + 1, 2, 1, minInt257 + 1)
          ]
        for c in checks do
          match c with
          | (x, y, shift, expected) =>
              expectOkStack s!"/unit/direct/x={x}/y={y}/shift={shift}"
                (runLshiftHashDivDirect shift #[intV x, intV y]) #[intV expected] }
    ,
    { name := "/unit/direct/hash-immediate-shift-does-not-pop-third-item"
      run := do
        expectOkStack "/unit/pop-order/residue-preserved"
          (runLshiftHashDivDirect 1 #[intV 99, intV 7, intV 3]) #[intV 99, intV 4] }
    ,
    { name := "/unit/error/intov-funnels-divzero-overflow-nan"
      run := do
        expectErr "/unit/intov/divzero/nonzero-over-zero"
          (runLshiftHashDivDirect 1 #[intV 7, intV 0]) .intOv
        expectErr "/unit/intov/overflow/max-shift1-div1"
          (runLshiftHashDivDirect 1 #[intV maxInt257, intV 1]) .intOv
        expectErr "/unit/intov/overflow/min-shift1-div1"
          (runLshiftHashDivDirect 1 #[intV minInt257, intV 1]) .intOv
        expectErr "/unit/intov/nan-divisor-direct"
          (runLshiftHashDivDirect 1 #[intV 7, .int .nan]) .intOv
        expectErr "/unit/intov/nan-numerator-direct"
          (runLshiftHashDivDirect 1 #[.int .nan, intV 3]) .intOv
        expectErr "/unit/intov/out-of-range-numerator-direct"
          (runLshiftHashDivDirect 1 #[intV (maxInt257 + 1), intV 3]) .intOv }
    ,
    { name := "/unit/error/underflow-and-pop-order"
      run := do
        expectErr "/unit/underflow/empty" (runLshiftHashDivDirect 1 #[]) .stkUnd
        expectErr "/unit/underflow/one-int" (runLshiftHashDivDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/underflow/one-non-int" (runLshiftHashDivDirect 1 #[.null]) .stkUnd
        expectErr "/unit/type/pop-y-first-null"
          (runLshiftHashDivDirect 1 #[intV 1, .null]) .typeChk
        expectErr "/unit/type/pop-y-first-cell"
          (runLshiftHashDivDirect 1 #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "/unit/type/pop-x-second-null"
          (runLshiftHashDivDirect 1 #[.null, intV 1]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-when-both-non-int"
          (runLshiftHashDivDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/error/invalid-immediate-shift-range-before-pop"
      run := do
        let invalidLow : Instr := .arithExt (.shlDivMod 1 (-1) false false (some 0))
        let invalidHigh : Instr := .arithExt (.shlDivMod 1 (-1) false false (some 257))
        expectErr "/unit/error-order/underflow-before-range-invalid-immediate"
          (runHandlerDirect execInstrArithExt invalidLow #[]) .stkUnd
        expectErr "/unit/error-order/range-before-y-type-invalid-immediate-low"
          (runHandlerDirect execInstrArithExt invalidLow #[.null, intV 7]) .rangeChk
        expectErr "/unit/error-order/range-before-y-type-invalid-immediate-high"
          (runHandlerDirect execInstrArithExt invalidHigh #[.cell Cell.empty, intV 7]) .rangeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let i17 := lshiftHashDivInstr 17
        let program : Array Instr := #[i17, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/lshift-hash-div" s0 i17 24
        let s2 ← expectDecodeStep "/unit/decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-shldivmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runLshiftHashDivDispatchFallback #[]) #[intV 9304] }
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
    mkShiftCase "/ok/pop-order/hash-immediate-does-not-pop-third-item" 7 3 1
      {} 1_000_000 |>.modifyInitStack (fun _ => #[intV 99, intV 7, intV 3]),
    mkShiftCase "/intov/divzero/nonzero-over-zero" 7 0 1,
    mkShiftCase "/intov/divzero/zero-over-zero" 0 0 256,
    mkShiftCase "/intov/overflow/max-shift1-div1" maxInt257 1 1,
    mkShiftCase "/intov/overflow/min-shift1-div1" minInt257 1 1,
    mkCase "/underflow/empty-stack" #[] #[lshiftHashDivInstrDefault],
    mkCase "/underflow/one-int" #[intV 1] #[lshiftHashDivInstrDefault],
    mkCase "/underflow/one-non-int-underflow-before-type" #[.null] #[lshiftHashDivInstrDefault],
    mkCase "/type/pop-y-first-null" #[intV 1, .null] #[lshiftHashDivInstrDefault],
    mkCase "/type/pop-y-first-cell" #[intV 1, .cell Cell.empty] #[lshiftHashDivInstrDefault],
    mkCase "/type/pop-x-second-null" #[.null, intV 1] #[lshiftHashDivInstrDefault],
    mkCase "/error-order/pop-y-before-x-when-both-non-int" #[.null, .cell Cell.empty] #[lshiftHashDivInstrDefault],
    mkInputCase "/intov/nan-divisor-via-program" (.num 7) .nan 1,
    mkInputCase "/intov/nan-numerator-via-program" .nan (.num 3) 1,
    mkInputCase "/error-order/pushint-overflow-x-before-op" (.num (maxInt257 + 1)) (.num 3) 1,
    mkInputCase "/error-order/pushint-overflow-y-before-op" (.num 7) (.num (maxInt257 + 1)) 1,
    mkInputCase "/error-order/pushint-overflow-both-before-op"
      (.num (maxInt257 + 1)) (.num (minInt257 - 1)) 1,
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num lshiftHashDivSetGasExact), .tonEnvOp .setGasLimit, lshiftHashDivInstrDefault],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num lshiftHashDivSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftHashDivInstrDefault]
  ]
  fuzz := #[
    { seed := 2026020857
      count := 700
      gen := genLshiftHashDivFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFT_HASH_DIV
