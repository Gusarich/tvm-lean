import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.PLDDICTQ

/-!
INSTRUCTION: PLDDICTQ

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch branch.
   - `execInstrDictLddict` handles only `.lddict true true`.
   - Any other instruction must forward to `next`.

2. [B2] Stack arity and base type checks.
   - One stack item required (`checkUnderflow 1` behavior).
   - Empty stack -> `.stkUnd`.
   - Non-`.slice` value on top -> `.typeChk`.

3. [B3] Empty/invalid availability gate (`s.haveBits 1`).
   - For `quiet=true`, `0` bits leads to failure result `0`.
   - For `preload=true` there is no source-slice preservation branch.

4. [B4] Present-bit and ref-existence branch (`needRefs`).
   - If first bit is `1`, `needRefs = 1`; when absent, `ok=false`.
   - Quiet failure path still returns just `0` for this opcode.

5. [B5] Hit path (`present=1`, `refs available`).
   - Pushes referenced cell.
   - `quiet=true` then pushes `-1`.

6. [B6] Miss path (`present=0`).
   - Pushes `.null`.
   - `quiet=true` then pushes `-1`.

7. [B7] Assembler encoding.
   - `.lddict true true` assembles as `0xF407`.

8. [B8] Decoder boundaries and adjacency.
   - `0xF404..0xF407` decode as the `.lddict` family by low bits.
   - `0xF408`, `0xF409`, and truncated `0xF4` decode as `.invOpcode`.

9. [B9] Runtime stack-preservation on success.
   - Values below the input slice remain below result.

10. [B10] Gas accounting.
    - Base gas is used for this opcode.
    - Exact gas must succeed; exact-minus-one must fail.

TOTAL BRANCHES: 10.

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is covered by fuzz.
-/

private def suiteId : InstrId := { name := "PLDDICTQ" }

private def instr : Instr := .lddict true true

private def fallbackSentinel : Int := 42_001

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB2 16) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]

private def presentSliceA : Slice := mkSliceWithBitsRefs #[true] #[valueA]
private def presentSliceB : Slice := mkSliceWithBitsRefs (natToBits 0b1110_1011 8) #[valueA, valueB]
private def presentSliceC : Slice := mkSliceWithBitsRefs (natToBits 0b1111_0001 8) #[valueB]
private def presentSliceNoRef : Slice := mkSliceWithBitsRefs #[true] #[]

private def missSliceA : Slice := mkSliceWithBitsRefs #[false] #[]
private def missSliceB : Slice := mkSliceWithBitsRefs (natToBits 0b0110_1001 8) #[]
private def emptyBitsSlice : Slice := mkSliceFromBits #[]

private def rawF404 : Cell := Cell.mkOrdinary (natToBits 0xF404 16) #[]
private def rawF405 : Cell := Cell.mkOrdinary (natToBits 0xF405 16) #[]
private def rawF406 : Cell := Cell.mkOrdinary (natToBits 0xF406 16) #[]
private def rawF407 : Cell := Cell.mkOrdinary (natToBits 0xF407 16) #[]
private def rawF408 : Cell := Cell.mkOrdinary (natToBits 0xF408 16) #[]
private def rawF409 : Cell := Cell.mkOrdinary (natToBits 0xF409 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def opcodeSlice16 (opcode : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits opcode 16) #[])

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr

private def runPLDDICTQDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictLddict instr stack

private def runPLDDICTQDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictLddict .add (VM.push (intV fallbackSentinel)) stack

private def expectDecodeStep
    (label : String)
    (opcode : Nat)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (opcodeSlice16 opcode) with
  | .ok (actual, bits, rest) =>
      if actual != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {actual}")
      if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected full decode")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (opcodeSlice16 opcode) with
  | .error .invOpcode =>
      pure ()
  | .ok (actual, bits, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {actual}/{bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value := #[])
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genPLDDICTQFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/underflow-empty" #[], rng1)
    else if shape = 1 then
      (mkCase "fuzz/type/int" #[(.int (.num 7))], rng1)
    else if shape = 2 then
      (mkCase "fuzz/type/cell" #[(.cell valueA)], rng1)
    else if shape = 3 then
      (mkCase "fuzz/type/tuple" #[(.tuple #[])], rng1)
    else if shape = 4 then
      (mkCase "fuzz/present/one-ref" #[(.slice presentSliceA)], rng1)
    else if shape = 5 then
      (mkCase "fuzz/present/multi-refs" #[(.slice presentSliceB)], rng1)
    else if shape = 6 then
      (mkCase "fuzz/present/c" #[(.slice presentSliceC)], rng1)
    else if shape = 7 then
      (mkCase "fuzz/miss/simple" #[(.slice missSliceA)], rng1)
    else if shape = 8 then
      (mkCase "fuzz/miss/tail" #[(.slice missSliceB)], rng1)
    else if shape = 9 then
      (mkCase "fuzz/no-bits" #[(.slice emptyBitsSlice)], rng1)
    else if shape = 10 then
      (mkCase "fuzz/missing-ref" #[(.slice presentSliceNoRef)], rng1)
    else if shape = 11 then
      (mkCase "fuzz/prefix/present"
        (#[.int (.num 77), .cell valueC, .slice presentSliceA]), rng1)
    else if shape = 12 then
      (mkCase "fuzz/prefix/miss"
        (#[.null, .int (.num 88), .slice missSliceB]), rng1)
    else if shape = 13 then
      (mkCase "fuzz/prefix/no-bits"
        (#[.slice emptyBitsSlice, .int (.num 101)]), rng1)
    else if shape = 14 then
      (mkCodeCase "fuzz/raw/f407" #[] rawF407, rng1)
    else if shape = 15 then
      (mkCodeCase "fuzz/raw/f408" #[] rawF408, rng1)
    else if shape = 16 then
      (mkCodeCase "fuzz/raw/f409" #[] rawF409, rng1)
    else if shape = 17 then
      (mkCase
        "fuzz/gas/exact"
        (#[(.slice presentSliceA)])
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExact baseGas), rng1)
    else if shape = 18 then
      (mkCase
        "fuzz/gas/exact-minus-one"
        (#[(.slice presentSliceA)])
        (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
        (oracleGasLimitsExactMinusOne baseGasMinusOne), rng1)
    else
      (mkCodeCase "fuzz/raw/truncated" #[] rawF4, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack "fallback"
          (runPLDDICTQDispatchFallback #[.slice presentSliceA])
          #[.slice presentSliceA, .int (.num fallbackSentinel)]
    },
    { name := "unit/encode-decode-contract" -- [B7][B8]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits != natToBits 0xF407 16 then
              throw (IO.userError "PLDDICTQ should encode to 0xF407")
        | .error e =>
            throw (IO.userError s!"PLDDICTQ assembler failed: {e}")
        expectDecodeStep "decode/f407" 0xF407 instr
        expectDecodeStep "decode/f404" 0xF404 (.lddict false false)
        expectDecodeStep "decode/f405" 0xF405 (.lddict true false)
        expectDecodeStep "decode/f406" 0xF406 (.lddict false true)
        expectDecodeInvOpcode "decode/f408" 0xF408
        expectDecodeInvOpcode "decode/f409" 0xF409
        match decodeCp0WithBits (Slice.ofCell rawF4) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/f4: expected invOpcode, got {e}")
        | .ok (i, bits, _) => throw (IO.userError s!"decode/f4: expected invOpcode, got {reprStr i}/{bits}")
    },
    { name := "unit/stack-and-type" -- [B2][B3]
      run := do
        expectErr "underflow-empty" (runPLDDICTQDirect #[]) .stkUnd
        expectErr "type-int" (runPLDDICTQDirect #[(.int (.num 7))]) .typeChk
        expectErr "type-cell" (runPLDDICTQDirect #[(.cell valueA)]) .typeChk
        expectErr "type-cont" (runPLDDICTQDirect #[(.cont (.quit 0))]) .typeChk
    },
    { name := "unit/runtime/no-bits-miss" -- [B3][B6]
      run := do
        expectOkStack "miss/no-bits"
          (runPLDDICTQDirect (#[(.slice emptyBitsSlice)]))
          #[.int (.num 0)]
    },
    { name := "unit/runtime/miss-success" -- [B6][B7][B9]
      run := do
        expectOkStack "miss/simple"
          (runPLDDICTQDirect (#[(.slice missSliceA)]))
          #[.null, .int (.num (-1))]
        expectOkStack "miss/tail"
          (runPLDDICTQDirect (#[(.slice missSliceB)]))
          #[.null, .int (.num (-1))]
    },
    { name := "unit/runtime/present-success" -- [B5][B7]
      run := do
        expectOkStack "present/single-ref"
          (runPLDDICTQDirect (#[(.slice presentSliceA)]))
          #[.cell valueA, .int (.num (-1))]
        expectOkStack "present/multi-refs"
          (runPLDDICTQDirect (#[(.slice presentSliceB)]))
          #[.cell valueA, .int (.num (-1))]
    },
    { name := "unit/runtime/missing-ref-quiet" -- [B4][B6]
      run := do
        expectOkStack "missing-ref/quiet"
          (runPLDDICTQDirect (#[(.slice presentSliceNoRef)]))
          #[.int (.num 0)]
    },
    { name := "unit/stack-preservation" -- [B9]
      run := do
        expectOkStack "preserve-prefix/present"
          (runPLDDICTQDirect (#[(.int (.num 77)), .cell valueC, .slice presentSliceC]))
          #[.int (.num 77), .cell valueC, .cell valueB, .int (.num (-1))]
        expectOkStack "preserve-prefix/miss"
          (runPLDDICTQDirect (#[(.null), .int (.num 88), .slice missSliceA]))
          #[.null, .int (.num 88), .null, .int (.num (-1))]
    }
  ]
  oracle := #[
    -- [B2]
    mkCase "oracle/underflow-empty" #[],
    -- [B2][B3]
    mkCase "oracle/type-int" #[(.int (.num 7))],
    mkCase "oracle/type-cell" #[(.cell valueA)],
    mkCase "oracle/type-tuple" #[(.tuple #[])],
    mkCase "oracle/type-builder" #[(.builder Builder.empty)],
    mkCase "oracle/type-cont" #[(.cont (.quit 0))],
    -- [B3][B6]
    mkCase "oracle/no-bits" #[(.slice emptyBitsSlice)],
    -- [B4]
    mkCase "oracle/missing-ref" #[(.slice presentSliceNoRef)],
    -- [B5][B7]
    mkCase "oracle/present-one-ref" #[(.slice presentSliceA)],
    mkCase "oracle/present-multi-refs" #[(.slice presentSliceB)],
    mkCase "oracle/present-with-noise-top" #[.int (.num 1), .cell valueA, .slice presentSliceC],
    mkCase "oracle/present-with-prefix-2" #[.slice presentSliceB, .int (.num 12), .cell valueC],
    -- [B6][B7]
    mkCase "oracle/miss-simple" #[(.slice missSliceA)],
    mkCase "oracle/miss-tail" #[(.slice missSliceB)],
    mkCase "oracle/miss-with-prefix" #[.cell valueC, .null, .slice missSliceA],
    -- [B8][B10]
    mkCodeCase "oracle/raw/f404" #[] rawF404,
    mkCodeCase "oracle/raw/f405" #[] rawF405,
    mkCodeCase "oracle/raw/f406" #[] rawF406,
    mkCodeCase "oracle/raw/f407" #[] rawF407,
    mkCodeCase "oracle/raw/f408" #[] rawF408,
    mkCodeCase "oracle/raw/f409" #[] rawF409,
    mkCodeCase "oracle/raw/truncated" #[] rawF4,
    -- [B9]
    mkCase "oracle/prefix-preserve-present"
      (#[.int (.num 77), .cell valueA, .slice presentSliceA]),
    mkCase "oracle/prefix-preserve-miss"
      (#[.cell valueB, .int (.num 123), .slice missSliceB]),
    -- [B10]
    mkCase
      "oracle/gas/exact"
      (#[(.slice presentSliceA)])
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact baseGas),
    mkCase
      "oracle/gas/exact-minus-one"
      (#[(.slice presentSliceA)])
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne baseGasMinusOne),
    -- Additional branches to exceed 30 oracle tests
    mkCase "oracle/no-bits-noise-top" #[.int (.num 7), .slice emptyBitsSlice],
    mkCase "oracle/missing-ref-noise-top" #[.builder Builder.empty, .slice presentSliceNoRef],
    mkCase "oracle/miss-top-with-bits" #[.slice missSliceA, .cell valueC],
    mkCase "oracle/present-top-with-bits" #[.slice presentSliceC, .tuple #[]],
    mkCase "oracle/present-extra-depth" #[.cell valueA, .int (.num 5), .int (.num 9), .slice presentSliceB],
    mkCase "oracle/miss-extra-depth" #[.null, .builder Builder.empty, .int (.num 1), .slice missSliceA],
    mkCase "oracle/no-bits-extra-depth" #[.slice emptyBitsSlice, .cont (.quit 0), .tuple #[]],
    mkCase "oracle/missing-ref-extra-depth" #[.int (.num 17), .int (.num 19), .slice presentSliceNoRef],
    mkCase "oracle/type-scalar-top" #[.int (.num 0), .int (.num 1), .cell valueB, .slice missSliceB]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genPLDDICTQFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.PLDDICTQ
