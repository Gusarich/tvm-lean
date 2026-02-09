import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.RSHIFTR_HASH

/-
RSHIFTR# branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false false 1 0 false (some z)` specialization)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`rshiftPow2Round`, nearest/tie behavior, ties toward `+∞`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate SHR family `0xa934..0xa936`, `z ∈ [1, 256]`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, hash-immediate decode to `.shrMod ... (some z)`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`mul=false`, `add=false`, `d=1`, `roundMode=0`, `quiet=false`, `zOpt=some z`):
- Lean specialization: 6 branch sites / 8 terminal outcomes
  (dispatch/fallback; depth gate; `x` pop type; fixed round-mode guard;
   finite-vs-invalid (`NaN`) path; non-quiet push fit-vs-`intOv`).
- C++ specialization: 5 branch sites / 8 aligned terminal outcomes
  (const-shift decode path; underflow gate; `pop_int` type; invalid-input compatibility
   quotient path; non-quiet push fit-vs-overflow).

Key risk areas covered:
- hash-immediate shift is encoded and must never pop a runtime shift operand;
- nearest rounding ties must go toward `+∞` (e.g. `-1 >>R#1 = 0`);
- shift boundary behavior at `z=1`, `z=255`, `z=256`;
- strict error ordering for underflow/type and program-prelude failures;
- NaN/out-of-range values are oracle/fuzz injected via `PUSHINT` prelude only
  (never placed directly into `initStack`);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; RSHIFTR#`.
-/

private def rshiftrHashId : InstrId := { name := "RSHIFTR#" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkRshiftrHashInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod false false 1 0 false (some shift))

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := rshiftrHashId
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
  mkCase name stack #[mkRshiftrHashInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (x : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkRshiftrHashInstr shift
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stack) (programPrefix.push instr) gasLimits fuel

private def runRshiftrHashDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkRshiftrHashInstr shift) stack

private def runRshiftrHashDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9345)) stack

private def expectAssembleErr
    (label : String)
    (program : List Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 program with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {e}")

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

private def rshiftrHashGasProbeInstr : Instr :=
  mkRshiftrHashInstr 7

private def rshiftrHashSetGasExact : Int :=
  computeExactGasBudget rshiftrHashGasProbeInstr

private def rshiftrHashSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne rshiftrHashGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def smallSignedPool : Array Int :=
  #[-33, -17, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 17, 33]

private def pickNatFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickIntFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
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

private def classifyRshiftrHash (x : Int) (shift : Nat) : String :=
  let p : Int := intPow2 shift
  let qFloor : Int := floorDivPow2 x shift
  let rFloor : Int := x - qFloor * p
  if rFloor = 0 then
    "ok-exact"
  else if rFloor * 2 = p then
    "ok-tie"
  else
    "ok-inexact"

private def genRshiftrHashFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 18
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyRshiftrHash x shift
      (mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}/boundary-x" shift (.num x), r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyRshiftrHash x shift
      (mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}/signed-x" shift (.num x), r3)
    else if shape = 2 then
      let (x, r2) := pickIntFromPool tieNumeratorPool rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok-tie/shift1" 1 (.num x), r2)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/boundary/shift256" 256 (.num x), r2)
    else if shape = 4 then
      let (x, r2) := pickInt257Boundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/boundary/shift255" 255 (.num x), r2)
    else if shape = 5 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty" shift #[], r2)
    else if shape = 6 then
      let (shift, r2) := pickShiftBoundary rng1
      let (xLike, r3) := pickNonInt r2
      (mkShiftCase s!"/fuzz/shape-{shape}/type/top-non-int" shift #[xLike], r3)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let (below, r4) := pickNonInt r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/pop-order/below-preserved"
        shift (.num x) #[below], r4)
    else if shape = 8 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan-compat/x-nan-via-program" shift .nan, r2)
    else if shape = 9 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-high-before-op"
        1 (.num (maxInt257 + 1)), rng1)
    else if shape = 10 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-low-before-op"
        1 (.num (minInt257 - 1)), rng1)
    else if shape = 11 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      let (below, r4) := pickNonInt r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-with-below-non-int"
        shift (.num xOut) #[below], r4)
    else if shape = 12 then
      let (shift, r2) := pickShiftInRange rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok-exact/zero-x" shift (.num 0), r2)
    else if shape = 13 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/boundary/minus-one-shift256" 256 (.num (-1)), rng1)
    else if shape = 14 then
      let (x, r2) := pickIntFromPool smallSignedPool rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyRshiftrHash x shift
      (mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}/small-signed" shift (.num x), r3)
    else if shape = 15 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/boundary/max-shift1" 1 (.num maxInt257), rng1)
    else if shape = 16 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/boundary/min-shift1" 1 (.num minInt257), rng1)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (below, r3) := pickNonInt r2
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/type-top-before-below"
        1 #[intV x, below], r3)
    else
      let (x, r2) := pickIntFromPool #[-1, 1] rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok-tie/shift256-half" 256 (.num (x * (pow2 255))), r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := rshiftrHashId
  unit := #[
    { name := "/unit/direct/nearest-rounding-and-ties"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (7, 1, 4),
            (-7, 1, -3),
            (5, 1, 3),
            (-5, 1, -2),
            (1, 1, 1),
            (-1, 1, 0),
            (3, 1, 2),
            (-3, 1, -1),
            (9, 3, 1),
            (-9, 3, -1)
          ]
        for check in checks do
          match check with
          | (x, shift, expected) =>
              expectOkStack s!"/unit/direct/x={x}/z={shift}"
                (runRshiftrHashDirect shift #[intV x]) #[intV expected] }
    ,
    { name := "/unit/direct/boundary-shifts-and-sign-extension"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (maxInt257, 256, 1),
            (maxInt257 - 1, 256, 1),
            (minInt257, 256, -1),
            (minInt257 + 1, 256, -1),
            (pow2 255, 256, 1),
            (-(pow2 255), 256, 0),
            (maxInt257, 255, 2),
            (minInt257, 255, -2),
            (-1, 256, 0)
          ]
        for check in checks do
          match check with
          | (x, shift, expected) =>
              expectOkStack s!"/unit/boundary/x={x}/z={shift}"
                (runRshiftrHashDirect shift #[intV x]) #[intV expected] }
    ,
    { name := "/unit/direct/pop-order/hash-immediate-does-not-pop-below"
      run := do
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runRshiftrHashDirect 1 #[.null, intV 7]) #[.null, intV 4]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runRshiftrHashDirect 256 #[.cell Cell.empty, intV (-1)]) #[.cell Cell.empty, intV 0] }
    ,
    { name := "/unit/error/underflow-type-and-ordering"
      run := do
        expectErr "/unit/error/underflow/empty"
          (runRshiftrHashDirect 1 #[]) .stkUnd
        expectErr "/unit/error/type/top-null"
          (runRshiftrHashDirect 1 #[.null]) .typeChk
        expectErr "/unit/error/type/top-cell"
          (runRshiftrHashDirect 1 #[.cell Cell.empty]) .typeChk
        expectErr "/unit/error-order/type-top-before-below-null"
          (runRshiftrHashDirect 1 #[intV 7, .null]) .typeChk
        expectErr "/unit/error-order/type-top-before-below-cell"
          (runRshiftrHashDirect 1 #[intV 7, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkRshiftrHashInstr 1
        let instr256 := mkRshiftrHashInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/opcode/decode: assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/rshiftr-hash-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/rshiftr-hash-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/opcode/encode-invalid-immediate-range"
      run := do
        expectAssembleErr "/unit/encode/range/shift0" [mkRshiftrHashInstr 0] .rangeChk
        expectAssembleErr "/unit/encode/range/shift257" [mkRshiftrHashInstr 257] .rangeChk }
    ,
    { name := "/unit/dispatch/non-rshiftr-hash-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runRshiftrHashDispatchFallback #[]) #[intV 9345] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/nearest/sign/pos-shift1" 1 (.num 7),
    mkShiftInputCase "/ok/nearest/sign/neg-shift1" 1 (.num (-7)),
    mkShiftInputCase "/ok/nearest/tie/plus-half" 1 (.num 1),
    mkShiftInputCase "/ok/nearest/tie/minus-half" 1 (.num (-1)),
    mkShiftInputCase "/ok/nearest/tie/plus-three-halves" 1 (.num 3),
    mkShiftInputCase "/ok/nearest/tie/minus-three-halves" 1 (.num (-3)),
    mkShiftInputCase "/ok/nearest/inexact/pos-shift2" 2 (.num 7),
    mkShiftInputCase "/ok/nearest/inexact/neg-shift2" 2 (.num (-7)),
    mkShiftInputCase "/ok/nearest/inexact/pos-shift3" 3 (.num 9),
    mkShiftInputCase "/ok/nearest/inexact/neg-shift3" 3 (.num (-9)),
    mkShiftInputCase "/ok/boundary/max-shift256" 256 (.num maxInt257),
    mkShiftInputCase "/ok/boundary/max-minus-one-shift256" 256 (.num (maxInt257 - 1)),
    mkShiftInputCase "/ok/boundary/min-shift256" 256 (.num minInt257),
    mkShiftInputCase "/ok/boundary/min-plus-one-shift256" 256 (.num (minInt257 + 1)),
    mkShiftInputCase "/ok/boundary/plus-half-at-2^255-shift256" 256 (.num (pow2 255)),
    mkShiftInputCase "/ok/boundary/minus-half-at-2^255-shift256" 256 (.num (-(pow2 255))),
    mkShiftInputCase "/ok/boundary/max-shift255" 255 (.num maxInt257),
    mkShiftInputCase "/ok/boundary/min-shift255" 255 (.num minInt257),
    mkShiftInputCase "/ok/boundary/minus-one-shift256" 256 (.num (-1)),
    mkShiftInputCase "/ok/pop-order/hash-immediate-does-not-pop-below-null"
      1 (.num 7) #[.null],
    mkShiftInputCase "/ok/pop-order/hash-immediate-does-not-pop-below-cell"
      256 (.num (-1)) #[.cell Cell.empty],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/type/top-null" 1 #[.null],
    mkShiftCase "/type/top-cell" 1 #[.cell Cell.empty],
    mkShiftCase "/error-order/type-top-before-below-null" 1 #[intV 7, .null],
    mkShiftCase "/error-order/type-top-before-below-cell" 1 #[intV 7, .cell Cell.empty],
    mkShiftInputCase "/ok/nan-compat/x-nan-shift1-via-program" 1 .nan,
    mkShiftInputCase "/ok/nan-compat/x-nan-shift256-via-program" 256 .nan,
    mkShiftInputCase "/error-order/pushint-overflow-x-high-before-op"
      1 (.num (maxInt257 + 1)),
    mkShiftInputCase "/error-order/pushint-overflow-x-low-before-op"
      1 (.num (minInt257 - 1)),
    mkShiftInputCase "/error-order/pushint-overflow-before-op-with-below-non-int"
      1 (.num (maxInt257 + 1)) #[.null],
    mkCase "/gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num rshiftrHashSetGasExact), .tonEnvOp .setGasLimit, rshiftrHashGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num rshiftrHashSetGasExactMinusOne), .tonEnvOp .setGasLimit, rshiftrHashGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020889
      count := 700
      gen := genRshiftrHashFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFTR_HASH
