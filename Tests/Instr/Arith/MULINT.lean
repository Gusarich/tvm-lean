import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MULINT

/-
MULINT branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/MulInt.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_mul_tinyint8`, `register_add_mul_ops` for `MULINT` / `QMULINT`).

Branch counts used for this suite:
- Lean: 5 branch points / 6 terminal outcomes
  (opcode dispatch; `popInt` underflow/type/success split; `.nan` vs `.num`;
   non-quiet `pushIntQuiet` NaN throw path; signed-257 fit check on finite product).
- C++: 4 branch points / 6 terminal outcomes
  (`check_underflow(1)` pass/fail; `pop_int` type/success; multiply NaN-vs-finite;
   non-quiet `push_int_quiet` success vs `int_ov`, including NaN funneling).

Key divergence risk areas:
- tinyint8 sign extension at decode boundaries (`0x7f = 127`, `0x80 = -128`);
- assembler range checks for immediate domain `[-128, 127]`;
- non-quiet NaN handling (`MULINT` must throw `intOv`, not push NaN);
- signed 257-bit overflow/underflow at `±2^256`;
- single-pop error ordering (top-of-stack type error masks lower entries);
- exact-gas boundary in `PUSHINT n; SETGASLIMIT; MULINT k`.
-/

private def mulIntId : InstrId := { name := "MULINT" }

private def gasProbeImm : Int := 3

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.mulInt gasProbeImm])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := mulIntId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runMulIntDirect (n : Int) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithMulInt (.mulInt n) stack

private def failUnit (msg : String) : IO α :=
  throw (IO.userError msg)

private def expectRoundtripMulIntImm (label : String) (n : Int) : IO Unit := do
  match assembleCp0 [Instr.mulInt n] with
  | .error e =>
      failUnit s!"{label}: assemble failed: {e}"
  | .ok code =>
      match decodeCp0WithBits (Slice.ofCell code) with
      | .error e =>
          failUnit s!"{label}: decode failed: {e}"
      | .ok (.mulInt n', totBits, _) =>
          if totBits ≠ 16 then
            failUnit s!"{label}: expected 16-bit decode, got {totBits}"
          else if n' ≠ n then
            failUnit s!"{label}: expected immediate {n}, got {n'}"
          else
            pure ()
      | .ok (instr, _, _) =>
          failUnit s!"{label}: expected MULINT decode, got {instr}"

private def expectAssembleRangeChk (label : String) (n : Int) : IO Unit := do
  match assembleCp0 [Instr.mulInt n] with
  | .error .rangeChk => pure ()
  | .error e => failUnit s!"{label}: expected rangeChk, got {e}"
  | .ok _ => failUnit s!"{label}: expected assemble rangeChk, got success"

private def rawMulIntCell (immByte : Nat) : Cell :=
  let bits : BitString :=
    natToBits 0xa7 8 ++ natToBits immByte 8 ++ Array.replicate 16 false
  Cell.mkOrdinary bits (Array.replicate 4 Cell.empty)

private def expectDecodedMulIntImmByte
    (label : String) (immByte : Nat) (expected : Int) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell (rawMulIntCell immByte)) with
  | .error e =>
      failUnit s!"{label}: decode failed: {e}"
  | .ok (.mulInt n, totBits, _) =>
      if totBits ≠ 16 then
        failUnit s!"{label}: expected 16-bit decode, got {totBits}"
      else if n ≠ expected then
        failUnit s!"{label}: expected immediate {expected}, got {n}"
      else
        pure ()
  | .ok (instr, _, _) =>
      failUnit s!"{label}: expected MULINT decode, got {instr}"

private def mulIntSetGasExact : Int :=
  computeExactGasBudget (.mulInt gasProbeImm)

private def mulIntSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (.mulInt gasProbeImm)

private def tinyInt8BoundaryPool : Array Int :=
  #[-128, -127, -64, -2, -1, 0, 1, 2, 64, 126, 127]

private def pickTinyInt8Boundary (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (tinyInt8BoundaryPool.size - 1)
  (tinyInt8BoundaryPool[idx]!, rng')

private def pickTinyInt8FromShared (rng0 : StdGen) : Int × StdGen :=
  let (sample, rng1) := pickSigned257ish rng0
  let immByte : Nat := (Int.emod sample 256).toNat
  (natToIntSignedTwos immByte 8, rng1)

private def genMulIntFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  let (x, rng2) :=
    if shape ≤ 2 then
      pickInt257Boundary rng1
    else
      pickSigned257ish rng1
  let (imm, rng3) :=
    if shape = 0 || shape = 3 || shape = 6 then
      pickTinyInt8Boundary rng2
    else
      pickTinyInt8FromShared rng2
  let (tag, rng4) := randNat rng3 0 999_999
  (mkCase s!"fuzz/shape-{shape}-{tag}" #[intV x] #[.mulInt imm], rng4)

def suite : InstrSuite where
  id := mulIntId
  unit := #[
    { name := "unit/finite-sign-zero-and-immediate-corners"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 3, 21),
            (7, -3, -21),
            (-7, 3, -21),
            (-7, -3, 21),
            (maxInt257, 0, 0),
            (1, 127, 127),
            (1, -128, -128),
            (-1, -128, 128),
            (maxInt257, -1, -maxInt257)
          ]
        for c in checks do
          let x := c.1
          let n := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}*{n}" (runMulIntDirect n #[intV x]) #[intV expected] }
    ,
    { name := "unit/near-boundary-successes"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (maxInt257, 1, maxInt257),
            (minInt257, 1, minInt257),
            (maxInt257 - 1, 1, maxInt257 - 1),
            (minInt257 + 1, 1, minInt257 + 1),
            (maxInt257 / 2, 2, maxInt257 - 1),
            (minInt257 / 2 + 1, 2, minInt257 + 2),
            (minInt257 + 1, -1, maxInt257)
          ]
        for c in checks do
          let x := c.1
          let n := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}*{n}" (runMulIntDirect n #[intV x]) #[intV expected] }
    ,
    { name := "unit/overflow-boundaries-throw-intov"
      run := do
        expectErr "min*-1" (runMulIntDirect (-1) #[intV minInt257]) .intOv
        expectErr "max*2" (runMulIntDirect 2 #[intV maxInt257]) .intOv
        expectErr "min*2" (runMulIntDirect 2 #[intV minInt257]) .intOv
        expectErr "max*127" (runMulIntDirect 127 #[intV maxInt257]) .intOv }
    ,
    { name := "unit/nan-type-underflow-and-pop-order"
      run := do
        expectErr "nan*5" (runMulIntDirect 5 #[.int .nan]) .intOv
        expectErr "empty" (runMulIntDirect 5 #[]) .stkUnd
        expectErr "top-non-int-null" (runMulIntDirect 5 #[.null]) .typeChk
        expectErr "top-non-int-over-lower-int" (runMulIntDirect 5 #[intV 9, .cell Cell.empty]) .typeChk
        expectOkStack "top-int-over-lower-non-int" (runMulIntDirect 5 #[.null, intV 9]) #[.null, intV 45] }
    ,
    { name := "unit/immediate-encoding-and-decode-boundaries"
      run := do
        expectRoundtripMulIntImm "roundtrip/min" (-128)
        expectRoundtripMulIntImm "roundtrip/zero" 0
        expectRoundtripMulIntImm "roundtrip/max" 127
        expectAssembleRangeChk "encode/too-small" (-129)
        expectAssembleRangeChk "encode/too-large" 128
        expectDecodedMulIntImmByte "decode/0x00" 0x00 0
        expectDecodedMulIntImmByte "decode/0x7f" 0x7f 127
        expectDecodedMulIntImmByte "decode/0x80" 0x80 (-128)
        expectDecodedMulIntImmByte "decode/0xff" 0xff (-1) }
  ]
  oracle := #[
    mkCase "ok/zero-x-zero-imm" #[intV 0] #[.mulInt 0],
    mkCase "ok/pos-pos" #[intV 7] #[.mulInt 3],
    mkCase "ok/pos-neg" #[intV 7] #[.mulInt (-3)],
    mkCase "ok/neg-pos" #[intV (-7)] #[.mulInt 3],
    mkCase "ok/neg-neg" #[intV (-7)] #[.mulInt (-3)],
    mkCase "ok/zero-imm-with-max-x" #[intV maxInt257] #[.mulInt 0],
    mkCase "boundary/max-times-one" #[intV maxInt257] #[.mulInt 1],
    mkCase "boundary/min-times-one" #[intV minInt257] #[.mulInt 1],
    mkCase "boundary/max-times-neg-one" #[intV maxInt257] #[.mulInt (-1)],
    mkCase "boundary/min-plus-one-times-neg-one" #[intV (minInt257 + 1)] #[.mulInt (-1)],
    mkCase "boundary/max-minus-one-times-one" #[intV (maxInt257 - 1)] #[.mulInt 1],
    mkCase "boundary/min-plus-one-times-one" #[intV (minInt257 + 1)] #[.mulInt 1],
    mkCase "boundary/near-overflow-half-max-times-two" #[intV (maxInt257 / 2)] #[.mulInt 2],
    mkCase "boundary/near-underflow-half-min-plus-one-times-two" #[intV (minInt257 / 2 + 1)] #[.mulInt 2],
    mkCase "immediate/min-neg128-times-one" #[intV 1] #[.mulInt (-128)],
    mkCase "immediate/max-127-times-one" #[intV 1] #[.mulInt 127],
    mkCase "immediate/zero-times-random-x" #[intV 123456789] #[.mulInt 0],
    mkCase "overflow/min-times-neg-one" #[intV minInt257] #[.mulInt (-1)],
    mkCase "overflow/max-times-two" #[intV maxInt257] #[.mulInt 2],
    mkCase "overflow/max-times-127" #[intV maxInt257] #[.mulInt 127],
    mkCase "underflow/min-times-two" #[intV minInt257] #[.mulInt 2],
    mkCase "underflow/empty-stack" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "error-order/top-non-int-before-lower-int" #[intV 5, .null],
    mkCase "error-order/top-int-allows-lower-non-int" #[.null, intV 5],
    mkCase "nan/operand-via-program-direct" #[] #[.pushInt .nan, .mulInt 5],
    mkCase "nan/operand-via-program" #[intV 42] #[.pushInt .nan, .mulInt 5],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num mulIntSetGasExact), .tonEnvOp .setGasLimit, .mulInt gasProbeImm],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num mulIntSetGasExactMinusOne), .tonEnvOp .setGasLimit, .mulInt gasProbeImm]
  ]
  fuzz := #[
    { seed := 2026020802
      count := 600
      gen := genMulIntFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MULINT
