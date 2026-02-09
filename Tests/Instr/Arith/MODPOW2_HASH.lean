import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MODPOW2_HASH

/-
MODPOW2# branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false false 2 (-1) false (some z)` specialization)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`modPow2Round`, floor remainder semantics)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate MODPOW2# family `0xa938..0xa93a`, `z ∈ [1, 256]`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, 24-bit hash-immediate decode path with `z = arg8 + 1`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`mul=false`, `add=false`, `d=2`, `roundMode=-1`, `quiet=false`, `zOpt=some z`):
- Lean specialization: 6 branch sites / 7 terminal outcomes
  (dispatch/fallback; underflow gate; `x` pop type split; fixed round guard;
   numeric-vs-NaN split; non-quiet push success-vs-`intOv` funnel).
- C++ specialization: 6 branch sites / 7 aligned terminal outcomes
  (global-version remap/invalid-op guard; hash-immediate arity gate;
   `pop_int` type split; `d` switch; non-quiet push success-vs-`int_ov` funnel).

Key risk areas covered:
- hash-immediate discipline: shift comes from opcode (`z`), never from stack;
- boundary powers: `z=1`, `z=255`, `z=256`, plus assembler `rangeChk` at `z=0`/`257`;
- unary pop ordering and error precedence (`stkUnd` on empty, then top-item `typeChk`);
- non-quiet NaN/out-of-range behavior via serialization-safe program prelude injection only;
- exact gas cliff via `PUSHINT n; SETGASLIMIT; MODPOW2#`.
-/

private def modpow2HashId : InstrId := { name := "MODPOW2#" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkModpow2HashInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod false false 2 (-1) false (some shift))

private def modpow2HashInstrDefault : Instr :=
  mkModpow2HashInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[modpow2HashInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := modpow2HashId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkShiftCase
    (name : String)
    (shift : Nat)
    (x : Int)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name #[intV x] #[mkModpow2HashInstr shift] gasLimits fuel

private def mkShiftStackCase
    (name : String)
    (shift : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[mkModpow2HashInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (x : IntVal)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkModpow2HashInstr shift
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stack) (programPrefix.push instr) gasLimits fuel

private def runModpow2HashDirect
    (shift : Nat)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkModpow2HashInstr shift) stack

private def runModpow2HashDispatchFallback
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9381)) stack

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

private def modpow2HashGasProbeInstr : Instr :=
  mkModpow2HashInstr 7

private def modpow2HashSetGasExact : Int :=
  computeExactGasBudget modpow2HashGasProbeInstr

private def modpow2HashSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne modpow2HashGasProbeInstr

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shift256XPool : Array Int :=
  #[minInt257, minInt257 + 1, -1, 0, 1, maxInt257]

private def smallSignedPool : Array Int :=
  #[-42, -17, -13, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 13, 17, 42]

private def pickFromIntPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickFromNatPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromNatPool shiftBoundaryPool rng

private def pickShiftInRange (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 1 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  (if pickCell then .cell Cell.empty else .null, rng')

private def classifyModpow2Hash (x : Int) (shift : Nat) : String :=
  let r := modPow2Round x shift (-1)
  if r = 0 then "ok-exact" else "ok-inexact"

private def genModpow2HashFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyModpow2Hash x shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-x-boundary-z" shift x, r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyModpow2Hash x shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/signed-x-random-z" shift x, r3)
    else if shape = 2 then
      let (x, r2) := pickFromIntPool smallSignedPool rng1
      let (shift, r3) := pickShiftBoundary r2
      let kind := classifyModpow2Hash x shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/small-x-boundary-z" shift x, r3)
    else if shape = 3 then
      let (useMax, r2) := randBool rng1
      let x := if useMax then maxInt257 else minInt257
      let kind := classifyModpow2Hash x 1
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift1-endpoint" 1 x, r2)
    else if shape = 4 then
      let (useMax, r2) := randBool rng1
      let x := if useMax then maxInt257 else minInt257
      let kind := classifyModpow2Hash x 255
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift255-endpoint" 255 x, r2)
    else if shape = 5 then
      let (x, r2) := pickFromIntPool shift256XPool rng1
      let kind := classifyModpow2Hash x 256
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift256" 256 x, r2)
    else if shape = 6 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/empty" shift #[], r2)
    else if shape = 7 then
      let (bad, r2) := pickNonInt rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/type/single-non-int" shift #[bad], r3)
    else if shape = 8 then
      let (shift, r2) := pickShiftBoundary rng1
      let (topBad, r3) := pickNonInt r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/top-item-before-below-int"
        shift #[intV 5, topBad], r3)
    else if shape = 9 then
      let (shift, r2) := pickShiftBoundary rng1
      let (topBad, r3) := pickNonInt r2
      (mkShiftStackCase s!"/fuzz/shape-{shape}/error-order/top-item-before-below-non-int"
        shift #[.null, topBad], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let (below, r4) := pickNonInt r3
      let kind := classifyModpow2Hash x shift
      (mkShiftStackCase s!"/fuzz/shape-{shape}/{kind}/pop-order/below-preserved"
        shift #[below, intV x], r4)
    else if shape = 11 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program" shift .nan, r2)
    else if shape = 12 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op"
        shift (.num xOut), r3)
    else if shape = 13 then
      let (shift, r2) := pickShiftInRange rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/ok-exact/x-zero" shift 0, r2)
    else if shape = 14 then
      let (xRaw, r2) := pickFromIntPool smallSignedPool rng1
      let x := if xRaw = 0 then 1 else xRaw
      let (shift, r3) := pickShiftInRange r2
      let kind := classifyModpow2Hash x shift
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/small-nonzero-x-random-z" shift x, r3)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let kind := classifyModpow2Hash x 256
      (mkShiftCase s!"/fuzz/shape-{shape}/{kind}/boundary-shift256-random-x" 256 x, r2)
    else
      (mkShiftStackCase s!"/fuzz/shape-{shape}/underflow/fallback" 1 #[], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := modpow2HashId
  unit := #[
    { name := "/unit/direct/floor-mod-sign-and-power-boundary-invariants"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (0, 1, 0),
            (7, 1, 1),
            (-7, 1, 1),
            (13, 3, 5),
            (-13, 3, 3),
            (42, 6, 42),
            (-42, 6, 22),
            (maxInt257, 1, 1),
            (minInt257, 1, 0),
            (maxInt257, 255, (pow2 255) - 1),
            (minInt257, 255, 0),
            (maxInt257, 256, maxInt257),
            (minInt257, 256, 0),
            (minInt257 + 1, 256, 1),
            (-1, 256, maxInt257)
          ]
        for c in checks do
          match c with
          | (x, shift, expected) =>
              expectOkStack s!"/unit/direct/x={x}/z={shift}"
                (runModpow2HashDirect shift #[intV x]) #[intV expected] }
    ,
    { name := "/unit/pop-order/immediate-does-not-pop-below-item"
      run := do
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runModpow2HashDirect 3 #[.null, intV 13]) #[.null, intV 5]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runModpow2HashDirect 2 #[.cell Cell.empty, intV (-13)]) #[.cell Cell.empty, intV 3] }
    ,
    { name := "/unit/error/underflow-type-and-top-item-ordering"
      run := do
        expectErr "/unit/error/underflow-empty"
          (runModpow2HashDirect 1 #[]) .stkUnd
        expectErr "/unit/error/type-single-null"
          (runModpow2HashDirect 1 #[.null]) .typeChk
        expectErr "/unit/error/type-single-cell"
          (runModpow2HashDirect 1 #[.cell Cell.empty]) .typeChk
        expectErr "/unit/error-order/top-item-before-below-int"
          (runModpow2HashDirect 4 #[intV 7, .null]) .typeChk
        expectErr "/unit/error-order/top-item-before-below-non-int"
          (runModpow2HashDirect 4 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/hash-immediate-encode-decode-and-range"
      run := do
        expectAssembleErr "/unit/opcode/encode/shift-0-rangechk"
          [mkModpow2HashInstr 0] .rangeChk
        expectAssembleErr "/unit/opcode/encode/shift-257-rangechk"
          [mkModpow2HashInstr 257] .rangeChk
        let instr1 := mkModpow2HashInstr 1
        let instr256 := mkModpow2HashInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"/unit/opcode/assemble-failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/opcode/decode/modpow2-hash-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/opcode/decode/modpow2-hash-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/opcode/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/opcode/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-shrmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runModpow2HashDispatchFallback #[]) #[intV 9381] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/floor/basic/shift1-pos" 1 (.num 7),
    mkShiftInputCase "/ok/floor/basic/shift1-neg" 1 (.num (-7)),
    mkShiftInputCase "/ok/floor/basic/shift3-pos" 3 (.num 13),
    mkShiftInputCase "/ok/floor/basic/shift3-neg" 3 (.num (-13)),
    mkShiftInputCase "/ok/floor/basic/shift6-pos" 6 (.num 42),
    mkShiftInputCase "/ok/floor/basic/shift6-neg" 6 (.num (-42)),
    mkShiftInputCase "/ok/boundary/shift255-max" 255 (.num maxInt257),
    mkShiftInputCase "/ok/boundary/shift255-min" 255 (.num minInt257),
    mkShiftInputCase "/ok/boundary/shift256-max" 256 (.num maxInt257),
    mkShiftInputCase "/ok/boundary/shift256-min" 256 (.num minInt257),
    mkShiftInputCase "/ok/boundary/shift256-min-plus-one" 256 (.num (minInt257 + 1)),
    mkShiftInputCase "/ok/boundary/shift256-neg-one" 256 (.num (-1)),
    mkShiftStackCase "/ok/pop-order/below-null-preserved" 3 #[.null, intV 13],
    mkShiftStackCase "/ok/pop-order/below-cell-preserved" 2 #[.cell Cell.empty, intV (-13)],
    mkShiftStackCase "/underflow/empty-stack" 1 #[],
    mkShiftStackCase "/type/single-null" 1 #[.null],
    mkShiftStackCase "/type/single-cell" 1 #[.cell Cell.empty],
    mkShiftStackCase "/error-order/top-item-before-below-int" 4 #[intV 7, .null],
    mkShiftStackCase "/error-order/top-item-before-below-non-int" 4 #[.null, .cell Cell.empty],
    mkShiftInputCase "/intov/nan-x-via-program" 5 .nan,
    mkShiftInputCase "/error-order/pushint-overflow-before-op-pos" 5 (.num (maxInt257 + 1)),
    mkShiftInputCase "/error-order/pushint-overflow-before-op-neg" 5 (.num (minInt257 - 1)),
    mkCase "/gas/exact-cost-succeeds" #[intV 37]
      #[.pushInt (.num modpow2HashSetGasExact), .tonEnvOp .setGasLimit, modpow2HashGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 37]
      #[.pushInt (.num modpow2HashSetGasExactMinusOne), .tonEnvOp .setGasLimit, modpow2HashGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020894
      count := 700
      gen := genModpow2HashFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MODPOW2_HASH
