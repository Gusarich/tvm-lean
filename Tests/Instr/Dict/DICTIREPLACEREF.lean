import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIREPLACEREF

/-!
INSTRUCTION: DICTIREPLACEREF

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch path.
   - `.dictSet` is handled by `execInstrDictDictSet`; other instructions must fall
     through to `next` without consuming stack.

2. [B2] Stack preamble: underflow and type checks.
   - `checkUnderflow 4` is mandatory.
   - Pops are in order: `n`, `dict`, `key`, `valRef`.
   - `popMaybeCell` and `popCell` can raise `typeChk`.

3. [B3] `n` and int-key conversion validation.
   - `popNatUpTo 1023` enforces key width and rejects NaN/negative/too-large.
   - `dictKeyBits?` enforces signed int-key bounds for the chosen width.

4. [B4] Replace success vs miss.
   - Hit replaces/rebuilds value and pushes updated root + `-1`.
   - Miss returns old root (or `null`) and pushes `0`.

5. [B5] By-ref value requirement.
   - `DICTIREPLACEREF` always follows by-ref path; value must be a `cell`.

6. [B6] Signed integer key boundaries.
   - `intKey=true`, `unsigned=false`, so ranges are signed:
     - `n=0` accepts only key `0`.
     - `n=1` accepts only `-1` and `0`.
     - wider widths constrain accordingly.

7. [B7] Assembler boundary behavior.
   - Exact encode is `0xF425`.
   - Non-int-key/unsigned combinations in this opcode family must reject.
   - Neighbor opcodes in `0xF422..0xF427` decode to different dict ops.

8. [B8] Decoder stream behavior.
   - Valid neighbors must decode at 16-bit boundaries.
   - Truncated opcode should fail to decode.

9. [B9] Gas accounting.
   - Base budget success and minus-one failure on miss path.
   - Replace-hit path adds `cellCreateGasPrice * created`.

TOTAL BRANCHES: 9

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTIREPLACEREF" }

private def instr : Instr :=
  .dictSet true false true .replace

private def dictNull : Value :=
  .null

private def valueA : Cell :=
  Cell.mkOrdinary (natToBits 0xA 8) #[]

private def valueB : Cell :=
  Cell.mkOrdinary (natToBits 0xB 8) #[]

private def valueC : Cell :=
  Cell.mkOrdinary (natToBits 0xC 8) #[]

private def badKeySlice : Slice :=
  mkSliceFromBits (natToBits 0xAA 8)

private def mkDictSetRefRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some b => b
        | none => panic! s!"{label}: invalid key/range ({k}, n={n})"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict construction"

private def mkDictSetRefReplaceCreated (root : Cell) (n : Nat) (key : Int) (newValue : Cell) : Nat :=
  match dictKeyBits? key n false with
  | some keyBits =>
      match dictSetRefWithCells (some root) keyBits newValue .replace with
      | .ok (_newRoot?, _ok, created, _loaded) => created
      | .error _ => 0
  | none => 0

private def dictSingle8 : Cell :=
  mkDictSetRefRoot! "dictSingle8" 8 #[(5, valueA)]

private def dictDouble8 : Cell :=
  mkDictSetRefRoot! "dictDouble8" 8 #[(5, valueA), (-1, valueB)]

private def dictTriple8 : Cell :=
  mkDictSetRefRoot! "dictTriple8" 8 #[(5, valueA), (-1, valueB), (1, valueC)]

private def dictSingle0 : Cell :=
  mkDictSetRefRoot! "dictSingle0" 0 #[(0, valueA)]

private def dictSingle257 : Cell :=
  mkDictSetRefRoot! "dictSingle257" 257 #[(0, valueA)]

private def singleHitCreated : Nat :=
  mkDictSetRefReplaceCreated dictSingle8 8 5 valueB

private def doubleHitCreated : Nat :=
  mkDictSetRefReplaceCreated dictDouble8 8 (-1) valueC

private def baseGas : Int :=
  computeExactGasBudget instr

private def baseGasMinusOne : Int :=
  computeExactGasBudgetMinusOne instr

private def hitSingleGas : Int :=
  baseGas + (Int.ofNat singleHitCreated * cellCreateGasPrice)

private def hitSingleGasMinusOne : Int :=
  if hitSingleGas > 0 then hitSingleGas - 1 else 0

private def hitDoubleGas : Int :=
  baseGas + (Int.ofNat doubleHitCreated * cellCreateGasPrice)

private def hitDoubleGasMinusOne : Int :=
  if hitDoubleGas > 0 then hitDoubleGas - 1 else 0

private def rawOpcodeF425 : Cell :=
  Cell.mkOrdinary (natToBits 0xF425 16) #[]
private def rawOpcodeF424 : Cell :=
  Cell.mkOrdinary (natToBits 0xF424 16) #[]
private def rawOpcodeF426 : Cell :=
  Cell.mkOrdinary (natToBits 0xF426 16) #[]
private def rawOpcodeF427 : Cell :=
  Cell.mkOrdinary (natToBits 0xF427 16) #[]
private def rawOpcodeTruncated8 : Cell :=
  Cell.mkOrdinary (natToBits 0xF4 8) #[]

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
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictIReplaceRefDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet .add (VM.push (intV 909)) stack

def genDICTIReplaceRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/ok/hit/single8" (#[ .cell dictSingle8, intV 8, intV 5, .cell valueB ]), rng1)
    else if shape = 1 then
      (mkCase "fuzz/ok/hit/double8" (#[ .cell dictDouble8, intV 8, intV (-1), .cell valueC ]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/ok/hit/zero-width" (#[ .cell dictSingle0, intV 0, intV 0, .cell valueA ]), rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/miss/null" (#[dictNull, intV 8, intV 6, .cell valueA]), rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/miss/narrow-width" (#[ .cell dictSingle8, intV 4, intV 5, .cell valueA ]), rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/miss/wide-n" (#[ .cell dictDouble8, intV 257, intV 0, .cell valueB ]), rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/program-trimmed" (#[ intV 777, .cell dictSingle8, intV 8, intV 5, .cell valueB ]), rng1)
    else if shape = 7 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 8 then
      (mkCase "fuzz/gas/miss-exact" (#[dictNull, intV 8, intV 0, .cell valueA])
        (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact baseGas), rng1)
    else if shape = 9 then
      (mkCase "fuzz/gas/miss-minus-one" (#[dictNull, intV 8, intV 0, .cell valueA])
        (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne baseGas), rng1)
    else if shape = 10 then
      (mkCase "fuzz/gas/hit-single-exact" (#[ .cell dictSingle8, intV 8, intV 5, .cell valueB ])
        (#[.pushInt (.num hitSingleGas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact hitSingleGas), rng1)
    else if shape = 11 then
      (mkCase "fuzz/gas/hit-single-minus-one" (#[ .cell dictSingle8, intV 8, intV 5, .cell valueB ])
        (#[.pushInt (.num hitSingleGasMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne hitSingleGas), rng1)
    else if shape = 12 then
      (mkCase "fuzz/gas/hit-double-exact" (#[ .cell dictDouble8, intV 8, intV (-1), .cell valueC ])
        (#[.pushInt (.num hitDoubleGas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact hitDoubleGas), rng1)
    else if shape = 13 then
      (mkCase "fuzz/gas/hit-double-minus-one" (#[ .cell dictDouble8, intV 8, intV (-1), .cell valueC ])
        (#[.pushInt (.num hitDoubleGasMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne hitDoubleGas), rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/type-dict" (#[ .tuple #[], intV 8, intV 5, .cell valueA ]), rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/type-key" (#[ .cell dictSingle8, intV 8, .slice badKeySlice, .cell valueA ]), rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/type-value" (#[ .cell dictSingle8, intV 8, intV 5, intV 5 ]), rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/nan-key" (#[ .cell dictSingle8, .int .nan, intV 5, .cell valueA ]), rng1)
    else if shape = 18 then
      (mkCase "fuzz/err/key-oob" (#[ .cell dictSingle8, intV 1, intV 1, .cell valueA ]), rng1)
    else
      (mkCodeCase "fuzz/code/raw/f425" #[.cell dictSingle8, intV 8, intV 5, .cell valueA] rawOpcodeF425, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 :=
  fuzzSeedForInstr suiteId

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st ←
          match runDictIReplaceRefDispatchFallback (#[intV 1, intV 2, intV 3, .cell valueA]) with
          | .ok s => pure s
          | .error e => throw (IO.userError s!"fallback failed with {e}")
        if st == #[intV 1, intV 2, intV 3, .cell valueA, intV 909] then
          pure ()
        else
          throw (IO.userError s!"fallback failed: expected {reprStr (#[intV 1, intV 2, intV 3, .cell valueA, intV 909])}, got {reprStr st}") },
    { name := "unit/opcode/assemble/exact" -- [B7]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF425 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF425 bits, got {reprStr c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble DICTIREPLACEREF failed: {reprStr e}") },
    { name := "unit/opcode/assemble/reject" -- [B7]
      run := do
        match assembleCp0 [ .dictSet false true true .replace ] with
        | .ok c =>
            throw (IO.userError s!"assemble unexpectedly accepted invalid flag combination: {reprStr c.bits}")
        | .error _ =>
            pure () },
    { name := "unit/decode/branches" -- [B8]
      run := do
        let s0 := Slice.ofCell rawOpcodeF425
        let _ ← expectDecodeStep "decode/f425" s0 instr 16
        let s1 := Slice.ofCell rawOpcodeF424
        let _ ← expectDecodeStep "decode/f424" s1 (.dictSet true false false .replace) 16
        let s2 := Slice.ofCell rawOpcodeF426
        let _ ← expectDecodeStep "decode/f426" s2 (.dictSet true true false .replace) 16
        let s3 := Slice.ofCell rawOpcodeF427
        let s4 ← expectDecodeStep "decode/f427" s3 (.dictSet true true true .replace) 16
        if s4.bitsRemaining + s4.refsRemaining != 0 then
          throw (IO.userError "decode did not consume all bits")
    },
    { name := "unit/decode/truncated" -- [B8]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawOpcodeTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted truncated opcode")
    }
  ]
  oracle := #[
    mkCase "ok/hit/single8" (#[ .cell dictSingle8, intV 8, intV 5, .cell valueB ]), -- [B4][B6]
    mkCase "ok/hit/double8-1" (#[ .cell dictDouble8, intV 8, intV (-1), .cell valueA ]), -- [B4][B6]
    mkCase "ok/hit/double8-2" (#[ .cell dictDouble8, intV 8, intV 5, .cell valueC ]), -- [B4][B6]
    mkCase "ok/hit/zero-width" (#[ .cell dictSingle0, intV 0, intV 0, .cell valueA ]), -- [B4][B6]
    mkCase "ok/hit/triple8" (#[ .cell dictTriple8, intV 8, intV 1, .cell valueA ]), -- [B4][B6]
    mkCase "ok/hit/program-trimmed-stack" (#[ intV 777, .cell dictSingle8, intV 8, intV 5, .cell valueB ]), -- [B4][B6]
    mkCase "ok/hit/wide-key" (#[ .cell dictSingle257, intV 257, intV 0, .cell valueB ]), -- [B4][B6]
    mkCase "ok/miss/null-8" (#[dictNull, intV 8, intV 5, .cell valueA]), -- [B4][B6]
    mkCase "ok/miss/null-0" (#[dictNull, intV 0, intV 0, .cell valueA]), -- [B4][B6][B6]
    mkCase "ok/miss/key-miss" (#[ .cell dictSingle8, intV 8, intV 6, .cell valueA ]), -- [B4][B6]
    mkCase "ok/miss/width-mismatch-8->4" (#[ .cell dictSingle8, intV 4, intV 5, .cell valueA ]), -- [B4][B6]
    mkCase "ok/miss/wide-width-257" (#[ .cell dictSingle8, intV 257, intV 1, .cell valueA ]), -- [B4][B6]
    mkCase "err/underflow/empty" (#[] : Array Value), -- [B2]
    mkCase "err/underflow/one-item" #[.cell dictSingle8], -- [B2]
    mkCase "err/underflow/two" #[.cell dictSingle8, intV 8], -- [B2]
    mkCase "err/underflow/three" #[.cell dictSingle8, intV 8, intV 5], -- [B2]
    mkCase "err/type/value-not-cell" (#[ .cell dictSingle8, intV 8, intV 5, intV 5 ]), -- [B5][B2]
    mkCase "err/type/dict-not-cell" (#[ .tuple #[], intV 8, intV 5, .cell valueA ]), -- [B2]
    mkCase "err/type/key-not-int" (#[ .cell dictSingle8, intV 8, .slice badKeySlice, .cell valueA ]), -- [B2][B3]
    mkCase "err/n/negative" (#[ .cell dictSingle8, intV (-1), intV 5, .cell valueA ]), -- [B3]
    mkCase "err/n/nan" (#[ .cell dictSingle8, .int .nan, intV 5, .cell valueA ]), -- [B3]
    mkCase "err/n/too-large" (#[ .cell dictSingle8, intV 1024, intV 5, .cell valueA ]), -- [B3]
    mkCase "err/key/out-of-range-n0" (#[ .cell dictSingle0, intV 0, intV 1, .cell valueA ]), -- [B6][B3]
    mkCase "err/key/out-of-range-n1" (#[ .cell dictSingle8, intV 1, intV 1, .cell valueA ]), -- [B6][B3]
    mkCase "err/key/out-of-range-n4" (#[ .cell dictSingle8, intV 4, intV (-9), .cell valueA ]), -- [B6][B3]
    mkCodeCase "ok/code/raw/f425" (#[ .cell dictSingle8, intV 8, intV 5, .cell valueA ]) rawOpcodeF425, -- [B7][B8]
    mkCodeCase "ok/code/raw/f424" (#[ .cell dictSingle8, intV 8, intV 5, .cell valueA ]) rawOpcodeF424, -- [B7][B8]
    mkCodeCase "ok/code/raw/f426" (#[ .cell dictSingle8, intV 8, intV 5, .cell valueA ]) rawOpcodeF426, -- [B7][B8]
    mkCodeCase "ok/code/raw/f427" (#[ .cell dictSingle8, intV 8, intV 5, .cell valueA ]) rawOpcodeF427, -- [B7][B8]
    mkCodeCase "err/code/truncated8" (#[] : Array Value) rawOpcodeTruncated8, -- [B8]
    mkCase "gas/base-exact-miss" (#[dictNull, intV 8, intV 5, .cell valueA ])
      (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact baseGas), -- [B9]
    mkCase "gas/base-exact-minus-one" (#[dictNull, intV 8, intV 5, .cell valueA ])
      (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne baseGas), -- [B9]
    mkCase "gas/hit-single-exact" (#[ .cell dictSingle8, intV 8, intV 5, .cell valueB ])
      (#[.pushInt (.num hitSingleGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitSingleGas), -- [B9]
    mkCase "gas/hit-single-minus-one" (#[ .cell dictSingle8, intV 8, intV 5, .cell valueB ])
      (#[.pushInt (.num hitSingleGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne hitSingleGas), -- [B9]
    mkCase "gas/hit-double-exact" (#[ .cell dictDouble8, intV 8, intV 5, .cell valueC ])
      (#[.pushInt (.num hitDoubleGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact hitDoubleGas) -- [B9]
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDICTIReplaceRefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIREPLACEREF
