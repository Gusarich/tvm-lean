import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.ADDRSHIFTC_HASH_MOD

/-
ADDRSHIFTC#MOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod false true 3 1 false (some z))` path)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate `0xa932 ++ (z-1)` arm)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeInstrCp0`, `0xa930..0xa932` decode to hash-immediate add+rshift/mod)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.popInt`, non-quiet `VM.pushIntQuiet`, underflow/type ordering)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, `dump_shrmod`, mode=`hash|non-quiet`, add-path remap)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch/terminal counts used for this suite
(`mul=false`, `add=true`, `d=3`, `roundMode=1`, `quiet=false`, `zOpt=some z`):
- Lean: 8 branch sites / 10 terminal outcomes
  (dispatch/fallback; underflow gate; `w` pop type; `x` pop type; round guard;
   numeric-vs-NaN split; add-path push funnel fit-vs-`intOv`; success pair terminal).
- C++: 8 branch sites / 10 aligned terminal outcomes
  (`d==0` add-remap; invalid-op guard; hash-immediate underflow gate;
   `w`/`x` `pop_int` checks; add-path execution; non-quiet push funnel).

Key risk areas covered:
- hash-immediate shift must not be popped from stack (`w` then `x` only);
- ceil quotient/remainder invariants across sign mixes and shift boundaries (`1`, `255`, `256`);
- strict error order: underflow before type, then `w` pop before `x`;
- non-quiet NaN funnel (`intOv`) via program-prelude injected NaN operands;
- oracle serialization constraints: NaN/out-of-range inputs injected via `PUSHINT` prelude only;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; ADDRSHIFTC#MOD`.
-/

private def addrshiftcHashModId : InstrId := { name := "ADDRSHIFTC#MOD" }

private def addrshiftcHashModInstr (shift : Nat) : Instr :=
  .arithExt (.shrMod false true 3 1 false (some shift))

private def addrshiftcHashModInstrDefault : Instr :=
  addrshiftcHashModInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[addrshiftcHashModInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := addrshiftcHashModId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkShiftCase
    (name : String)
    (x w : Int)
    (shift : Nat)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name #[intV x, intV w] #[addrshiftcHashModInstr shift] gasLimits fuel

private def mkInputCase
    (name : String)
    (x w : IntVal)
    (shift : Nat := 1)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram #[x, w]
  mkCase name stack (programPrefix.push (addrshiftcHashModInstr shift)) gasLimits fuel

private def runAddrshiftcHashModDirect (shift : Nat) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (addrshiftcHashModInstr shift) stack

private def runAddrshiftcHashModDispatchFallback (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 9332)) stack

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

private def addrshiftcHashModSetGasExact : Int :=
  computeExactGasBudget addrshiftcHashModInstrDefault

private def addrshiftcHashModSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne addrshiftcHashModInstrDefault

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tinyShiftPool : Array Nat :=
  #[1, 2, 3, 4, 5, 6, 7, 8]

private def smallSignedPool : Array Int :=
  #[-33, -17, -13, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 13, 17, 33]

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

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickCell, rng') := randBool rng
  (if pickCell then .cell Cell.empty else .null, rng')

private def classifyAddrshiftcHashMod (x w : Int) (shift : Nat) : String :=
  let q := rshiftPow2RoundAddCompat x w shift 1
  let r := modPow2Round (x + w) shift 1
  if !intFitsSigned257 q || !intFitsSigned257 r then
    "intov-overflow"
  else if r = 0 then
    "ok-exact"
  else
    "ok-inexact"

private def mkFiniteFuzzCase (shape : Nat) (x w : Int) (shift : Nat) : OracleCase :=
  let kind := classifyAddrshiftcHashMod x w shift
  mkShiftCase s!"/fuzz/shape-{shape}/{kind}" x w shift

private def genAddrshiftcHashModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (shift, r4) := pickFromNatPool shiftBoundaryPool r3
      (mkFiniteFuzzCase shape x w shift, r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkFiniteFuzzCase shape x w shift, r4)
    else if shape = 2 then
      let (x, r2) := pickFromIntPool smallSignedPool rng1
      let (w, r3) := pickFromIntPool smallSignedPool r2
      let (shift, r4) := pickFromNatPool tinyShiftPool r3
      (mkFiniteFuzzCase shape x w shift, r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkFiniteFuzzCase shape x 0 shift, r3)
    else if shape = 4 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkFiniteFuzzCase shape 0 w shift, r3)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkShiftCase s!"/fuzz/shape-{shape}/ok-exact/sum-zero" x (-x) shift, r3)
    else if shape = 6 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      (mkFiniteFuzzCase shape x w 1, r3)
    else if shape = 7 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickFromIntPool smallSignedPool r2
      (mkFiniteFuzzCase shape x w 256, r3)
    else if shape = 8 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-int" #[intV x], r2)
    else if shape = 10 then
      let (v, r2) := pickNonInt rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-non-int" #[v], r2)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (wLike, r3) := pickNonInt r2
      (mkCase s!"/fuzz/shape-{shape}/type/pop-w-first"
        #[intV x, wLike] #[addrshiftcHashModInstrDefault], r3)
    else if shape = 12 then
      let (w, r2) := pickSigned257ish rng1
      let (xLike, r3) := pickNonInt r2
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-second"
        #[xLike, intV w] #[addrshiftcHashModInstrDefault], r3)
    else if shape = 13 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-w-before-x-when-both-non-int"
        #[.null, .cell Cell.empty] #[addrshiftcHashModInstrDefault], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/pop-order/immediate-does-not-pop-third-item"
        #[intV 42, intV x, intV w] #[addrshiftcHashModInstr shift], r4)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkInputCase s!"/fuzz/shape-{shape}/intov-nan-w-via-program"
        (.num x) .nan shift, r3)
    else if shape = 16 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkInputCase s!"/fuzz/shape-{shape}/intov-nan-x-via-program"
        .nan (.num w) shift, r3)
    else if shape = 17 then
      let (x, r2) := pickInt257OutOfRange rng1
      let (shift, r3) := pickValidShift r2
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        (.num x) (.num 3) shift, r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickValidShift r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        (.num x) (.num w) shift, r4)
    else if shape = 19 then
      let (x, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickValidShift r3
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-both-before-op"
        (.num x) (.num w) shift, r4)
    else if shape = 20 then
      let (x, r2) := pickFromIntPool smallSignedPool rng1
      let (q, r3) := pickFromIntPool smallSignedPool r2
      let (shift, r4) := pickFromNatPool tinyShiftPool r3
      let w := q * intPow2 shift - x
      (mkShiftCase s!"/fuzz/shape-{shape}/ok-exact/constructed-divisible-sum" x w shift, r4)
    else
      (mkCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type"
        #[.null] #[addrshiftcHashModInstrDefault], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := addrshiftcHashModId
  unit := #[
    { name := "/unit/direct/ceil-rounding-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Nat × Int × Int) :=
          #[
            (7, 0, 1, 4, -1),
            (7, 1, 1, 4, 0),
            (-7, 0, 1, -3, -1),
            (-7, -1, 1, -4, 0),
            (5, -7, 1, -1, 0),
            (-5, 7, 1, 1, 0),
            (1, 0, 2, 1, -3),
            (-1, 0, 2, 0, -1),
            (0, 0, 256, 0, 0),
            (maxInt257, 0, 256, 1, -1),
            (minInt257, 0, 256, -1, 0),
            (maxInt257, minInt257, 1, 0, -1),
            (minInt257, maxInt257, 1, 0, -1)
          ]
        for c in checks do
          match c with
          | (x, w, shift, q, r) =>
              expectOkStack s!"/unit/direct/x={x}/w={w}/shift={shift}"
                (runAddrshiftcHashModDirect shift #[intV x, intV w]) #[intV q, intV r] }
    ,
    { name := "/unit/direct/hash-immediate-shift-does-not-pop-third-item"
      run := do
        expectOkStack "/unit/pop-order/residue-preserved"
          (runAddrshiftcHashModDirect 1 #[intV 99, intV 7, intV 0]) #[intV 99, intV 4, intV (-1)] }
    ,
    { name := "/unit/error/underflow-and-pop-order"
      run := do
        expectErr "/unit/underflow/empty" (runAddrshiftcHashModDirect 1 #[]) .stkUnd
        expectErr "/unit/underflow/one-int" (runAddrshiftcHashModDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/underflow/one-non-int" (runAddrshiftcHashModDirect 1 #[.null]) .stkUnd
        expectErr "/unit/type/pop-w-first-null"
          (runAddrshiftcHashModDirect 1 #[intV 1, .null]) .typeChk
        expectErr "/unit/type/pop-w-first-cell"
          (runAddrshiftcHashModDirect 1 #[intV 1, .cell Cell.empty]) .typeChk
        expectErr "/unit/type/pop-x-second-null"
          (runAddrshiftcHashModDirect 1 #[.null, intV 1]) .typeChk
        expectErr "/unit/error-order/pop-w-before-x-when-both-non-int"
          (runAddrshiftcHashModDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/opcode/decode-hash-immediate-sequence"
      run := do
        let i17 := addrshiftcHashModInstr 17
        let program : Array Instr := #[i17, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/addrshiftc-hash-mod" s0 i17 24
        let s2 ← expectDecodeStep "/unit/decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-shrmod-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runAddrshiftcHashModDispatchFallback #[]) #[intV 9332] }
  ]
  oracle := #[
    mkShiftCase "/ok/ceil/sign/pos-pos-shift1" 7 0 1,
    mkShiftCase "/ok/ceil/sign/neg-pos-shift1" (-7) 0 1,
    mkShiftCase "/ok/ceil/sign/pos-neg-shift1" 7 (-9) 1,
    mkShiftCase "/ok/ceil/sign/neg-neg-shift1" (-7) (-1) 1,
    mkShiftCase "/ok/ceil/exact/sum-divisible-shift1" 7 1 1,
    mkShiftCase "/ok/ceil/inexact/small-pos-shift2" 1 0 2,
    mkShiftCase "/ok/ceil/inexact/small-neg-shift2" (-1) 0 2,
    mkShiftCase "/ok/boundary/max-shift1" maxInt257 0 1,
    mkShiftCase "/ok/boundary/min-shift1" minInt257 0 1,
    mkShiftCase "/ok/boundary/max-shift256" maxInt257 0 256,
    mkShiftCase "/ok/boundary/min-shift256" minInt257 0 256,
    mkShiftCase "/ok/boundary/max-plus-min-shift1" maxInt257 minInt257 1,
    mkShiftCase "/ok/boundary/min-plus-max-shift1" minInt257 maxInt257 1,
    mkCase "/ok/pop-order/hash-immediate-does-not-pop-third-item"
      #[intV 99, intV 7, intV 0] #[addrshiftcHashModInstrDefault],
    mkCase "/underflow/empty-stack" #[] #[addrshiftcHashModInstrDefault],
    mkCase "/underflow/one-int" #[intV 1] #[addrshiftcHashModInstrDefault],
    mkCase "/underflow/one-non-int-underflow-before-type" #[.null] #[addrshiftcHashModInstrDefault],
    mkCase "/type/pop-w-first-null" #[intV 1, .null] #[addrshiftcHashModInstrDefault],
    mkCase "/type/pop-w-first-cell" #[intV 1, .cell Cell.empty] #[addrshiftcHashModInstrDefault],
    mkCase "/type/pop-x-second-null" #[.null, intV 1] #[addrshiftcHashModInstrDefault],
    mkCase "/error-order/pop-w-before-x-when-both-non-int"
      #[.null, .cell Cell.empty] #[addrshiftcHashModInstrDefault],
    mkInputCase "/intov/nan-w-via-program" (.num 7) .nan 1,
    mkInputCase "/intov/nan-x-via-program" .nan (.num 3) 1,
    mkInputCase "/error-order/pushint-overflow-x-before-op" (.num (maxInt257 + 1)) (.num 3) 1,
    mkInputCase "/error-order/pushint-overflow-w-before-op" (.num 7) (.num (maxInt257 + 1)) 1,
    mkInputCase "/error-order/pushint-overflow-both-before-op"
      (.num (maxInt257 + 1)) (.num (minInt257 - 1)) 1,
    mkCase "/gas/exact-cost-succeeds" #[intV 13, intV 3]
      #[.pushInt (.num addrshiftcHashModSetGasExact), .tonEnvOp .setGasLimit, addrshiftcHashModInstrDefault],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 13, intV 3]
      #[.pushInt (.num addrshiftcHashModSetGasExactMinusOne), .tonEnvOp .setGasLimit, addrshiftcHashModInstrDefault]
  ]
  fuzz := #[
    { seed := 2026020882
      count := 700
      gen := genAddrshiftcHashModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.ADDRSHIFTC_HASH_MOD
