import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.PUSHINT_4

/-
PUSHINT_4 branch-mapping notes (Lean + C++ reference):
- Lean reviewed files:
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits` tinyint4 prefix `0x7` immediate decode)
  - `TvmLean/Semantics/Exec/Stack/PushInt.lean`
    (`execInstrStackPushInt` dispatch + `.pushInt` handling)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`VM.pushIntQuiet` non-quiet signed-257 acceptance/failure)
- C++ reviewed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_push_tinyint4`, `register_int_const_ops`, shared prelude `exec_push_int`)

Branch counts used for this suite:
- Lean: 6 branch points / 8 terminal outcomes
  (tinyint4 prefix hit/miss and decoder bit-availability; stack handler dispatch;
   `.pushInt` payload split (`.nan` vs `.num`); non-quiet `pushIntQuiet` fit vs `intOv`).
- C++: 4 branch points / 6 aligned terminal outcomes
  (opcode-table dispatch to tinyint4 handler; tinyint4 fast success path;
   prelude long-PUSHINT length check and range acceptance vs overflow failure).

Key risk areas:
- tinyint4 two's-complement mapping must remain bijective on `[-5, 10]`.
- PUSHINT_4 must append exactly one value while preserving existing stack order.
- NaN/out-of-range injections must occur via program prelude (`PUSHINT*`) only.
- Out-of-range prelude PUSHINT must fail before PUSHINT_4 executes.
- Gas edge for `PUSHINT n; SETGASLIMIT; PUSHINT_4` must be exact and deterministic.
-/

private def pushInt4Id : InstrId := { name := "PUSHINT_4" }

private def mkPushInt4Instr (imm : Int) : Instr :=
  .pushInt (.num imm)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pushInt4Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkPushInt4Case
    (name : String)
    (imm : Int)
    (stack : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[mkPushInt4Instr imm] gasLimits fuel

private def runPushIntDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPushInt instr stack

private def runPushInt4Direct (imm : Int) (stack : Array Value) : Except Excno (Array Value) :=
  runPushIntDirect (mkPushInt4Instr imm) stack

private def runPushIntDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPushInt .add (VM.push (intV 777)) stack

private def failUnit (msg : String) : IO α :=
  throw (IO.userError msg)

private def tinyInt4Pool : Array Int :=
  #[-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

private def pickTinyInt4 (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (tinyInt4Pool.size - 1)
  (tinyInt4Pool[idx]!, rng')

private def pickPrefixStack (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let (len, rng1) := randNat rng0 0 3
  let mut rng := rng1
  let mut stack : Array Value := #[]
  for _ in [0:len] do
    let (shape, r2) := randNat rng 0 4
    rng := r2
    if shape = 0 then
      let (x, r3) := pickSigned257ish rng
      rng := r3
      stack := stack.push (intV x)
    else if shape = 1 then
      let (x, r3) := pickInt257Boundary rng
      rng := r3
      stack := stack.push (intV x)
    else if shape = 2 then
      stack := stack.push .null
    else if shape = 3 then
      stack := stack.push (.cell Cell.empty)
    else
      stack := stack.push (intV 0)
  return (stack, rng)

private def pushInt4GasProbeImm : Int := 7

private def pushInt4GasProbeInstr : Instr :=
  mkPushInt4Instr pushInt4GasProbeImm

private def pushInt4SetGasExact : Int :=
  computeExactGasBudget pushInt4GasProbeInstr

private def pushInt4SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pushInt4GasProbeInstr

private def genPushInt4FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  let (imm, rng2) := pickTinyInt4 rng1
  let (tag, rng3) := randNat rng2 0 999_999
  if shape = 0 then
    (mkPushInt4Case s!"fuzz/ok/plain-{tag}" imm, rng3)
  else if shape = 1 then
    let (stack, r4) := pickPrefixStack rng3
    (mkPushInt4Case s!"fuzz/ok/prefix-{tag}" imm stack, r4)
  else if shape = 2 then
    (mkCase s!"fuzz/nan/prelude-before-op-{tag}" #[] #[.pushInt .nan, mkPushInt4Instr imm], rng3)
  else if shape = 3 then
    let (z, r4) := pickInt257OutOfRange rng3
    let over := if z > maxInt257 then z else maxInt257 + 1
    (mkCase s!"fuzz/range/over-max-prelude-{tag}" #[] #[.pushInt (.num over), mkPushInt4Instr imm], r4)
  else if shape = 4 then
    let (z, r4) := pickInt257OutOfRange rng3
    let under := if z < minInt257 then z else minInt257 - 1
    (mkCase s!"fuzz/range/under-min-prelude-{tag}" #[] #[.pushInt (.num under), mkPushInt4Instr imm], r4)
  else if shape = 5 then
    let (exact, r4) := randBool rng3
    let budget := if exact then pushInt4SetGasExact else pushInt4SetGasExactMinusOne
    let gasKind := if exact then "exact" else "exact-minus-one"
    (mkCase s!"fuzz/gas/{gasKind}-{tag}" #[intV 13]
      #[.pushInt (.num budget), .tonEnvOp .setGasLimit, mkPushInt4Instr imm], r4)
  else if shape = 6 then
    (mkCase s!"fuzz/underflow/post-add-{tag}" #[] #[mkPushInt4Instr imm, .add], rng3)
  else
    (mkCase s!"fuzz/type/post-add-{tag}" #[.null] #[mkPushInt4Instr imm, .add], rng3)

def suite : InstrSuite where
  id := pushInt4Id
  unit := #[
    { name := "unit/direct/pushes-all-tinyint4-values"
      run := do
        for n in tinyInt4Pool do
          expectOkStack s!"push({n})/empty"
            (runPushInt4Direct n #[])
            #[intV n]
          expectOkStack s!"push({n})/prefix-int"
            (runPushInt4Direct n #[intV 42])
            #[intV 42, intV n] }
    ,
    { name := "unit/direct/preserves-stack-order"
      run := do
        expectOkStack "preserve/mixed-prefix"
          (runPushInt4Direct (-2) #[.null, intV 9, .cell Cell.empty])
          #[.null, intV 9, .cell Cell.empty, intV (-2)] }
    ,
    { name := "unit/direct/non-pushint-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runPushIntDispatchFallback #[])
          #[intV 777] }
    ,
    { name := "unit/direct/prelude-nan-and-range-errors"
      run := do
        expectOkStack "pushnan-direct"
          (runPushIntDirect (.pushInt .nan) #[])
          #[.int .nan]
        expectErr "prelude/over-max-intov"
          (runPushIntDirect (.pushInt (.num (maxInt257 + 1))) #[])
          .intOv
        expectErr "prelude/under-min-intov"
          (runPushIntDirect (.pushInt (.num (minInt257 - 1))) #[])
          .intOv }
    ,
    { name := "unit/codec/tinyint4-roundtrip-width-8"
      run := do
        for n in tinyInt4Pool do
          let expected := mkPushInt4Instr n
          let code ←
            match assembleCp0 [expected, .add] with
            | .ok cell => pure cell
            | .error e => failUnit s!"assemble/tinyint4/{n}: {e}"
          let s0 := Slice.ofCell code
          let s1 ←
            match decodeCp0WithBits s0 with
            | .error e => failUnit s!"decode/tinyint4/{n}/head: {e}"
            | .ok (instr, bits, s') =>
                if instr != expected then
                  failUnit s!"decode/tinyint4/{n}/head-instr: got {reprStr instr}"
                else if bits != 8 then
                  failUnit s!"decode/tinyint4/{n}/head-bits: expected 8, got {bits}"
                else
                  pure s'
          match decodeCp0WithBits s1 with
          | .error e => failUnit s!"decode/tinyint4/{n}/tail: {e}"
          | .ok (instr, bits, s2) =>
              if instr != .add then
                failUnit s!"decode/tinyint4/{n}/tail-instr: got {reprStr instr}"
              else if bits != 8 then
                failUnit s!"decode/tinyint4/{n}/tail-bits: expected 8, got {bits}"
              else if s2.bitsRemaining != 0 then
                failUnit s!"decode/tinyint4/{n}/tail-rest: expected 0 bits, got {s2.bitsRemaining}"
              else
                pure () }
    ,
    { name := "unit/codec/non-tinyint4-uses-wider-encodings"
      run := do
        let checks : Array Int := #[-6, 11, -128, 127]
        for n in checks do
          let expected : Instr := .pushInt (.num n)
          let code ←
            match assembleCp0 [expected] with
            | .ok cell => pure cell
            | .error e => failUnit s!"assemble/non-tinyint4/{n}: {e}"
          match decodeCp0WithBits (Slice.ofCell code) with
          | .error e => failUnit s!"decode/non-tinyint4/{n}: {e}"
          | .ok (instr, bits, rest) =>
              if instr != expected then
                failUnit s!"decode/non-tinyint4/{n}/instr: got {reprStr instr}"
              else if bits ≤ 8 then
                failUnit s!"decode/non-tinyint4/{n}/bits: expected > 8, got {bits}"
              else if rest.bitsRemaining != 0 then
                failUnit s!"decode/non-tinyint4/{n}/rest: expected 0 bits, got {rest.bitsRemaining}"
              else
                pure () }
  ]
  oracle := #[
    mkPushInt4Case "ok/min-minus-five" (-5),
    mkPushInt4Case "ok/max-plus-ten" 10,
    mkPushInt4Case "ok/zero" 0,
    mkPushInt4Case "ok/positive-seven" 7,
    mkPushInt4Case "ok/negative-minus-one" (-1),
    mkPushInt4Case "ok/prefix-int" 4 #[intV 99],
    mkPushInt4Case "ok/prefix-mixed" (-3) #[.null, intV 9, .cell Cell.empty],
    mkCase "ok/post-add-succeeds" #[intV 8] #[mkPushInt4Instr (-3), .add],
    mkCase "underflow/post-add-needs-two-args" #[] #[mkPushInt4Instr 6, .add],
    mkCase "type/post-add-second-pop-non-int" #[.null] #[mkPushInt4Instr 2, .add],
    mkCase "nan/prelude-pushnan-before-op" #[] #[.pushInt .nan, mkPushInt4Instr 1],
    mkCase "range/prelude-over-max-before-op" #[intV 42]
      #[.pushInt (.num (maxInt257 + 1)), mkPushInt4Instr 1],
    mkCase "range/prelude-under-min-before-op" #[intV 42]
      #[.pushInt (.num (minInt257 - 1)), mkPushInt4Instr 1],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num pushInt4SetGasExact), .tonEnvOp .setGasLimit, pushInt4GasProbeInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num pushInt4SetGasExactMinusOne), .tonEnvOp .setGasLimit, pushInt4GasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020804
      count := 600
      gen := genPushInt4FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.PUSHINT_4
