import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.MODPOW2R_HASH

/-
MODPOW2R# branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false false 2 0 false (some z)` specialization)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate MODPOW2R# opcode family `0xa938..0xa93a`,
     immediate `z ∈ [1, 256]`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, `0xa938..0xa93a` decode to
     `.shrMod false false 2 ... (some z)`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, `VM.pushIntQuiet`, underflow/type behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, hash-immediate MODPOW2R# wiring in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`mul=false`, `add=false`, `d=2`, `roundMode=0`, `quiet=false`, `zOpt=some z`):
- Lean specialization: 4 branch sites / 5 terminal outcomes
  (dispatch/fallback; depth gate; `x` pop type split;
   finite-vs-NaN input with non-quiet push success-vs-`intOv`).
- C++ specialization: 4 branch sites / 5 aligned terminal outcomes
  (opcode route; underflow check; `pop_int` type split;
   `push_int_quiet` success-vs-`int_ov`).

Key risk areas covered:
- hash-immediate decode/encode boundaries (`z=1`, `z=256`, reject `z=0`/`257`);
- nearest rounding (`R`) remainder behavior on odd/tie and signed inputs;
- single-pop stack behavior (underflow/type ordering and lower-stack preservation);
- NaN/out-of-range injection via `PUSHINT` prelude only;
- exact gas cliff (`PUSHINT n; SETGASLIMIT; MODPOW2R#`) exact vs exact-minus-one.
-/

private def modPow2RHashId : InstrId := { name := "MODPOW2R#" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkModPow2RHashInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod false false 2 0 false (some shift))

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := modPow2RHashId
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
  mkCase name stack #[mkModPow2RHashInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkModPow2RHashInstr shift
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (programPrefix.push instr) gasLimits fuel

private def runModPow2RHashDirect (shift : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkModPow2RHashInstr shift) stack

private def runModPow2RHashDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9439)) stack

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

private def modPow2RHashGasProbeInstr : Instr :=
  mkModPow2RHashInstr 7

private def modPow2RHashSetGasExact : Int :=
  computeExactGasBudget modPow2RHashGasProbeInstr

private def modPow2RHashSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne modPow2RHashGasProbeInstr

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieCasePool : Array (Int × Nat) :=
  #[
    (3, 1), (-3, 1),
    (6, 2), (-6, 2),
    (12, 3), (-12, 3),
    (pow2 255, 256), (-(pow2 255), 256)
  ]

private def smallSignedPool : Array Int :=
  #[-17, -13, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 13, 17]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 1 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  ((if pickCell then .cell Cell.empty else .null), rng')

private def genModPow2RHashFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/boundary" shift #[.num x], r3)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/random" shift #[.num x], r3)
    else if shape = 2 then
      let ((x, shift), r2) := pickFromPool tieCasePool rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/rounding-tie-sensitive" shift #[.num x], r2)
    else if shape = 3 then
      let (pickMax, r2) := randBool rng1
      let x := if pickMax then maxInt257 else minInt257
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/extreme-x" shift #[.num x], r3)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/lower-null-preserved" shift #[.null, intV x], r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftCase s!"/fuzz/shape-{shape}/ok/lower-cell-preserved" shift #[.cell Cell.empty, intV x], r3)
    else if shape = 6 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty" shift #[], r2)
    else if shape = 7 then
      let (shift, r2) := pickShiftInRange rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/type/top-null" shift #[.null], r2)
    else if shape = 8 then
      let (shift, r2) := pickShiftInRange rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/type/top-cell" shift #[.cell Cell.empty], r2)
    else if shape = 9 then
      let (shift, r2) := pickShiftInRange rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov/nan-x-via-program" shift #[.nan], r2)
    else if shape = 10 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op" shift #[.num xOut], r3)
    else if shape = 11 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-before-op-type-check"
        #[.null] #[.pushInt (.num xOut), mkModPow2RHashInstr shift], r3)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/boundary/shift1" 1 #[.num x], r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/boundary/shift256" 256 #[.num x], r2)
    else if shape = 14 then
      let (x, r2) := pickFromPool smallSignedPool rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/small-signed" shift #[.num x], r3)
    else if shape = 15 then
      let (pickPos, r2) := randBool rng1
      let x := if pickPos then pow2 255 else -(pow2 255)
      (mkShiftInputCase s!"/fuzz/shape-{shape}/boundary/pow255-shift256" 256 #[.num x], r2)
    else if shape = 16 then
      let (pickMax, r2) := randBool rng1
      let x := if pickMax then maxInt257 - 1 else minInt257 + 1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/boundary/near-extreme-shift256" 256 #[.num x], r2)
    else
      let (nonInt, r2) := pickNonInt rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftCase s!"/fuzz/shape-{shape}/type/top-random-non-int" shift #[nonInt], r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := modPow2RHashId
  unit := #[
    { name := "/unit/direct/rounding-sensitive-remainders"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (3, 1, -1),
            (-3, 1, -1),
            (5, 2, 1),
            (-5, 2, -1),
            (6, 2, -2),
            (-6, 2, -2),
            (7, 3, -1),
            (-7, 3, 1),
            (17, 4, 1),
            (-17, 4, -1)
          ]
        for check in checks do
          match check with
          | (x, shift, expected) =>
              expectOkStack s!"/unit/direct/x={x}/z={shift}"
                (runModPow2RHashDirect shift #[intV x]) #[intV expected] }
    ,
    { name := "/unit/direct/boundary-and-lower-stack-preservation"
      run := do
        let checks : Array (Int × Nat × Int) :=
          #[
            (maxInt257, 256, -1),
            (maxInt257 - 1, 256, -2),
            (minInt257, 256, 0),
            (minInt257 + 1, 256, 1),
            (pow2 255, 256, -(pow2 255)),
            (-(pow2 255), 256, -(pow2 255))
          ]
        for check in checks do
          match check with
          | (x, shift, expected) =>
              expectOkStack s!"/unit/boundary/x={x}/z={shift}"
                (runModPow2RHashDirect shift #[intV x]) #[intV expected]
        expectOkStack "/unit/pop-order/lower-null-preserved"
          (runModPow2RHashDirect 1 #[.null, intV 3]) #[.null, intV (-1)]
        expectOkStack "/unit/pop-order/lower-cell-preserved"
          (runModPow2RHashDirect 2 #[.cell Cell.empty, intV (-5)])
          #[.cell Cell.empty, intV (-1)] }
    ,
    { name := "/unit/error/underflow-type-and-ordering"
      run := do
        expectErr "/unit/error/underflow-empty"
          (runModPow2RHashDirect 1 #[]) .stkUnd
        expectErr "/unit/error/type-top-null"
          (runModPow2RHashDirect 1 #[.null]) .typeChk
        expectErr "/unit/error/type-top-cell"
          (runModPow2RHashDirect 1 #[.cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let instr1 := mkModPow2RHashInstr 1
        let instr256 := mkModPow2RHashInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/opcode/assemble: failed with {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/opcode/decode-modpow2r-hash-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/opcode/decode-modpow2r-hash-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/opcode/decode-tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/opcode/decode-end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/opcode/encode-invalid-immediate-range"
      run := do
        let invalidLow := mkModPow2RHashInstr 0
        let invalidHigh := mkModPow2RHashInstr 257
        match assembleCp0 [invalidLow] with
        | .ok _ =>
            throw (IO.userError "/unit/opcode/encode/shift0: expected rangeChk, got ok")
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"/unit/opcode/encode/shift0: expected rangeChk, got {e}")
        match assembleCp0 [invalidHigh] with
        | .ok _ =>
            throw (IO.userError "/unit/opcode/encode/shift257: expected rangeChk, got ok")
        | .error e =>
            if e = .rangeChk then
              pure ()
            else
              throw (IO.userError s!"/unit/opcode/encode/shift257: expected rangeChk, got {e}") }
    ,
    { name := "/unit/dispatch/non-modpow2r-hash-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runModPow2RHashDispatchFallback #[]) #[intV 9439] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/round/shift1-pos-odd" 1 #[.num 3],
    mkShiftInputCase "/ok/round/shift1-neg-odd" 1 #[.num (-3)],
    mkShiftInputCase "/ok/round/shift2-pos-nontie" 2 #[.num 5],
    mkShiftInputCase "/ok/round/shift2-neg-nontie" 2 #[.num (-5)],
    mkShiftInputCase "/ok/round/shift2-pos-tie" 2 #[.num 6],
    mkShiftInputCase "/ok/round/shift2-neg-tie" 2 #[.num (-6)],
    mkShiftInputCase "/ok/round/shift3-pos-nontie" 3 #[.num 7],
    mkShiftInputCase "/ok/round/shift3-neg-nontie" 3 #[.num (-7)],
    mkShiftInputCase "/ok/round/shift4-pos" 4 #[.num 17],
    mkShiftInputCase "/ok/round/shift4-neg" 4 #[.num (-17)],
    mkShiftInputCase "/ok/boundary/max-shift256" 256 #[.num maxInt257],
    mkShiftInputCase "/ok/boundary/max-minus-one-shift256" 256 #[.num (maxInt257 - 1)],
    mkShiftInputCase "/ok/boundary/min-shift256" 256 #[.num minInt257],
    mkShiftInputCase "/ok/boundary/min-plus-one-shift256" 256 #[.num (minInt257 + 1)],
    mkShiftInputCase "/ok/boundary/pow255-shift256" 256 #[.num (pow2 255)],
    mkShiftInputCase "/ok/boundary/negpow255-shift256" 256 #[.num (-(pow2 255))],
    mkShiftCase "/ok/pop-order/lower-null-preserved" 1 #[.null, intV 3],
    mkShiftCase "/ok/pop-order/lower-cell-preserved" 2 #[.cell Cell.empty, intV (-5)],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/type/x-top-null" 1 #[.null],
    mkShiftCase "/type/x-top-cell" 1 #[.cell Cell.empty],
    mkShiftInputCase "/intov/nan-x-via-program" 5 #[.nan],
    mkShiftInputCase "/error-order/pushint-overflow-high-before-op"
      5 #[.num (maxInt257 + 1)],
    mkShiftInputCase "/error-order/pushint-overflow-low-before-op"
      5 #[.num (minInt257 - 1)],
    mkCase "/error-order/pushint-overflow-before-op-type-check" #[.null]
      #[.pushInt (.num (maxInt257 + 1)), mkModPow2RHashInstr 7],
    mkCase "/gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num modPow2RHashSetGasExact), .tonEnvOp .setGasLimit, modPow2RHashGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num modPow2RHashSetGasExactMinusOne), .tonEnvOp .setGasLimit, modPow2RHashGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020853
      count := 700
      gen := genModPow2RHashFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.MODPOW2R_HASH
