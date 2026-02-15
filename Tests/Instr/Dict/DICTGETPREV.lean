import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTGETPREV

/-!
INSTRUCTION: DICTGETPREV (execInstrDictDictGetNear, C++ `exec_dict_getnear`)

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatcher path.
   - `.dictGetNear` is handled; any other opcode must be passed to `next` via
     `runHandlerDirectWithNext`.

2. [B2] Runtime preconditions.
   - Stack underflow for the required 3 items (`n`, dict root, key hint/key int).
   - `n` must be a finite int inside `popNatUpTo` bound.
   - dict root must satisfy `popMaybeCell`.
   - key is parsed according to key-mode (`popSlice` for slice mode; `popIntFinite`
     for int mode).

3. [B3] Assembler validation.
   - `.dictGetNear` accepts only `4 ≤ args4 ≤ 15`.
   - out-of-range values must raise `.rangeChk`.

4. [B4] Decoder behavior.
   - `0xf474..0xf47f` decode to `.dictGetNear args4`.
   - Adjacent family opcode `0xf480` / truncated encodings must fail decode.

5. [B5] Dictionary/key-mode semantics.
   - `args4 & 8 = 0` selects slice-key path and requires at least `n` bits.
   - `args4 & 8 = 8` selects int-key path; keys may be unsigned (bit 2 set) or signed.
   - For int mode, out-of-range key triggers fallback branch depending on sign and `goUp`.

6. [B6] Integer fallback and comparison branch.
   - On out-of-range int key, `cond` path chooses between
     immediate miss and min/max fallback.
   - Result is still miss (`0`) or nearest match depending on key/sign.

7. [B7] Dictionary traversal errors propagate.
   - `dictNearestWithCells` / `dictMinMaxWithCells` errors propagate as `dictErr`.

8. [B8] Gas accounting.
   - Base budget path and miss path should exactly consume base gas.
   - Slice-key hit path adds `cellCreateGasPrice` for key reconstruction.

9. [B9] Success/miss stack shape.
   - Miss pushes `0`.
   - Hit (slice key) pushes value slice, key slice, then `-1`.
   - Hit (int key) pushes value slice, integer key, then `-1`.

TOTAL BRANCHES: 9

Any branch not covered by oracle tests must be covered by fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTGETPREV" }

private def instr : Instr := .dictGetNear 4

private def dispatchSentinel : Int := 909

private def rawOpcode (args4 : Nat) : Cell :=
  Cell.mkOrdinary (natToBits (0xf470 + args4) 16) #[]

private def mkSlice (width : Nat) (value : Nat) : Slice :=
  mkSliceFromBits (natToBits value width)

private def mkSliceV (width : Nat) (value : Nat) : Value :=
  .slice (mkSlice width value)

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n true with
        | some b => b
        | none =>
            match dictKeyBits? k n false with
            | some b => b
            | none => panic! s!"{label}: invalid key/range ({k}, n={n})"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) => root := root1
      | .ok (none, _ok, _created, _loaded) => panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e => panic! s!"{label}: dict set failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dictionary after insertions"

private def valueA : Slice := mkSlice 8 0xAA
private def valueB : Slice := mkSlice 8 0x55
private def valueC : Slice := mkSlice 8 0x77

private def dictSlice4 : Cell :=
  mkDictSetSliceRoot! "dictSlice4" 4 #[(0, valueA), (5, valueB), (14, valueC)]

private def dictSlice8 : Cell :=
  mkDictSetSliceRoot! "dictSlice8" 8 #[(0, valueA), (1, valueB), (255, valueC)]

private def dictInt8Signed : Cell :=
  mkDictSetSliceRoot! "dictInt8Signed" 8 #[(0, valueA), (1, valueB), (-1, valueC)]

private def dictInt8Unsigned : Cell :=
  mkDictSetSliceRoot! "dictInt8Unsigned" 8 #[(0, valueA), (1, valueB), (2, valueC)]

private def dictInt257Signed : Cell :=
  mkDictSetSliceRoot! "dictInt257Signed" 257 #[(0, valueA), (1, valueB), (-1, valueC)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def sliceHitGas : Int := baseGas + cellCreateGasPrice
private def sliceHitGasMinusOne : Int := if sliceHitGas > 0 then sliceHitGas - 1 else 0

private def rawF474 : Cell := rawOpcode 4
private def rawF475 : Cell := rawOpcode 5
private def rawF47F : Cell := rawOpcode 15
private def rawF47A : Cell := rawOpcode 10
private def rawF47B : Cell := rawOpcode 11
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF47 12) #[]

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

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetNear .add (VM.push (intV dispatchSentinel)) stack

private def expectAssembleRangeErr (label : String) (badInstr : Instr) : IO Unit := do
  match assembleCp0 [badInstr] with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected .rangeChk, got success")
  | .error e =>
      if e = .rangeChk then
        pure ()
      else
        throw (IO.userError s!"{label}: expected .rangeChk, got {reprStr e}")

private def runDispatchCheck (stack : Array Value) : IO Unit := do
  expectOkStack "unit/dispatch/fallback" (runDispatchFallback stack) #[intV dispatchSentinel]

def genDictGetPrevFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  let (baseCase, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/slice/miss/null/4" (#[] ++ #[ .null, intV 4, mkSliceV 4 0 ]), rng1)
    else if shape = 1 then
      (mkCase "fuzz/slice/hit-eq/4" (#[] ++ #[ .cell dictSlice4, intV 4, mkSliceV 4 5 ])
        (program := #[.dictGetNear 5]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/slice/hit-eq/8" (#[] ++ #[ .cell dictSlice8, intV 8, mkSliceV 8 255 ])
        (program := #[.dictGetNear 5]), rng1)
    else if shape = 3 then
      (mkCase "fuzz/slice/underflow-key-bits" (#[] ++ #[ .cell dictSlice8, intV 8, mkSliceV 4 5 ]), rng1)
    else if shape = 4 then
      (mkCase "fuzz/int/signed-eq/8" (#[] ++ #[ .cell dictInt8Signed, intV 8, intV 1 ])
        (program := #[.dictGetNear 13]), rng1)
    else if shape = 5 then
      (mkCase "fuzz/int/unsigned-eq/8" (#[] ++ #[ .cell dictInt8Unsigned, intV 8, intV 1 ])
        (program := #[.dictGetNear 9]), rng1)
    else if shape = 6 then
      (mkCase "fuzz/int/cond-false-large" (#[] ++ #[ .cell dictInt8Signed, intV 8, intV 200 ])
        (program := #[.dictGetNear 12]), rng1)
    else if shape = 7 then
      (mkCase "fuzz/int/cond-true-large" (#[] ++ #[ .cell dictInt8Signed, intV 8, intV (-200) ])
        (program := #[.dictGetNear 12]), rng1)
    else if shape = 8 then
      (mkCase "fuzz/int/type-key-error" (#[] ++ #[ .cell dictInt8Signed, intV 8, .null ])
        (program := #[.dictGetNear 12]), rng1)
    else if shape = 9 then
      (mkCase "fuzz/int/type-root-error" (#[] ++ #[ .int (.num 17), intV 8, intV 1 ])
        (program := #[.dictGetNear 12]), rng1)
    else if shape = 10 then
      (mkCase "fuzz/int/malformed-root" (#[] ++ #[ .cell malformedDict, intV 8, intV 1 ])
        (program := #[.dictGetNear 13]), rng1)
    else if shape = 11 then
      (mkCase "fuzz/slice/malformed-root" (#[] ++ #[ .cell malformedDict, intV 8, mkSliceV 8 1 ])
        (program := #[.dictGetNear 4]), rng1)
    else if shape = 12 then
      (mkCodeCase "fuzz/slice/raw/f474" (#[] ++ #[ .cell dictSlice4, intV 4, mkSliceV 4 5 ]) rawF474, rng1)
    else if shape = 13 then
      (mkCase "fuzz/int/underflow-gas" (#[] ++ #[ .cell dictInt8Unsigned, intV 8, intV 1 ])
        (program := #[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, .dictGetNear 9])
        (gasLimits := oracleGasLimitsExact baseGas), rng1)
    else if shape = 14 then
      (mkCase "fuzz/int/oog-gas" (#[] ++ #[ .cell dictInt8Unsigned, intV 8, intV 1 ])
        (program := #[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, .dictGetNear 9])
        (gasLimits := oracleGasLimitsExact baseGasMinusOne), rng1)
    else if shape = 15 then
      (mkCodeCase "fuzz/int/raw/f47B" (#[] ++ #[ .cell dictInt8Signed, intV 8, intV 1 ]) rawF47B, rng1)
    else
      (mkCodeCase "fuzz/slice/raw/f47F" (#[] ++ #[ .cell dictSlice4, intV 4, mkSliceV 4 5 ]) rawF47F, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ baseCase with name := s!"{baseCase.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch-fallback" -- [B1]
      run := do
        runDispatchCheck #[] },
    { name := "unit/encode/ok/f474" -- [B3]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xf474 16 then
              pure ()
            else
              throw (IO.userError s!"unexpected bits {c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble .dictGetNear 4 failed: {reprStr e}") },
    { name := "unit/encode/reject-lower-args4" -- [B3]
      run := do
        expectAssembleRangeErr "unit/encode/reject-lower-args4" (.dictGetNear 3) },
    { name := "unit/encode/reject-upper-args4" -- [B3]
      run := do
        expectAssembleRangeErr "unit/encode/reject-upper-args4" (.dictGetNear 16) },
    { name := "unit/decode/family-boundary" -- [B4]
      run := do
        let packed :=
          Cell.mkOrdinary (rawF474.bits ++ rawF475.bits ++ rawF47F.bits) #[]
        let s0 := Slice.ofCell packed
        let s1 ← expectDecodeStep "decode/F474" s0 (.dictGetNear 4) 16
        let s2 ← expectDecodeStep "decode/F475" s1 (.dictGetNear 5) 16
        let _  ← expectDecodeStep "decode/F47F" s2 (.dictGetNear 15) 16
        pure () },
    { name := "unit/decode/adjacent-opcode" -- [B4]
      run := do
        let _ ← expectDecodeStep "unit/decode/adjacent-opcode" (Slice.ofCell rawF47F) (.dictGetNear 15) 16
        pure () },
    { name := "unit/decode/truncated-or-invalid" -- [B4]
      run := do
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ =>
            pure ()
        | .ok (i, _, _) =>
            throw (IO.userError s!"expected decode failure, got {reprStr i}") }
  ]
  oracle := #[
    mkCase "err/underflow/empty" #[] -- [B2]
      ,
    mkCase "err/underflow/one-item" (#[] ++ #[ .null ]) -- [B2]
      ,
    mkCase "err/underflow/two-item" (#[] ++ #[ .cell dictSlice4, intV 8 ]) -- [B2]
      ,
    mkCase "err/n-not-int" (#[] ++ #[ .cell dictSlice4, .null, mkSliceV 4 0 ]) -- [B2]
      ,
    mkCase "err/n-nan-int" (#[] ++ #[ .cell dictInt8Signed, .int (.nan), intV 5 ])
      (program := #[.dictGetNear 12]) -- [B2]
      ,
    mkCase "err/root-type-error-slice" (#[] ++ #[ .int (.num 17), intV 8, mkSliceV 8 1 ])
      (program := #[.dictGetNear 4]) -- [B2]
      ,
    mkCase "err/key-type-error-int" (#[] ++ #[ .cell dictInt8Signed, intV 8, .null ])
      (program := #[.dictGetNear 12]) -- [B2]
      ,
    mkCase "err/key-type-error-slice" (#[] ++ #[ .cell dictSlice4, intV 4, .null ]) -- [B2]
      ,
    mkCase "err/n-negative" (#[] ++ #[ .cell dictSlice4, intV (-1), mkSliceV 4 0 ]) -- [B2]
      ,
    mkCase "err/n-out-of-range-int" (#[] ++ #[ .cell dictInt8Signed, intV 258, intV 1 ])
      (program := #[.dictGetNear 12]) -- [B3]
      ,
    mkCase "err/n-out-of-range-slice" (#[] ++ #[ .cell dictSlice8, intV 1024, mkSliceV 8 1 ]) -- [B3]
      ,
    mkCase "err/root-type-error" (#[] ++ #[ .null, intV 8, intV 1 ])
      (program := #[.dictGetNear 12]) -- [B2]
      ,
    mkCase "err/key-slice-too-short" (#[] ++ #[ .cell dictSlice8, intV 8, mkSliceV 2 1 ]) -- [B6]
      ,
    mkCase "err/slice-root-malformed" (#[] ++ #[ .cell malformedDict, intV 8, mkSliceV 8 0 ]) -- [B7]
      ,
    mkCase "ok/slice/miss-empty" (#[] ++ #[ .null, intV 4, mkSliceV 4 0 ]) -- [B9]
      ,
    mkCase "ok/slice/hit-prev" (#[] ++ #[ .cell dictSlice4, intV 4, mkSliceV 4 5 ])
      (program := #[.dictGetNear 5]) -- [B5][B9]
      ,
    mkCase "ok/slice/hit-next-neighbor" (#[] ++ #[ .cell dictSlice4, intV 4, mkSliceV 4 5 ])
      (program := #[.dictGetNear 4]) -- [B5][B9]
      ,
    mkCase "ok/slice/hit-intmode-255" (#[] ++ #[ .cell dictSlice8, intV 8, mkSliceV 8 255 ])
      (program := #[.dictGetNear 5]) -- [B5]
      ,
    mkCase "ok/int/cond-false-out-of-range" (#[] ++ #[ .cell dictInt8Signed, intV 8, intV 200 ])
      (program := #[.dictGetNear 12]) -- [B6][B5]
      ,
    mkCase "ok/int/cond-false-out-of-range-unsigned" (#[] ++ #[ .cell dictInt8Unsigned, intV 8, intV (-1) ])
      (program := #[.dictGetNear 8]) -- [B6][B5]
      ,
    mkCase "ok/int/cond-true-out-of-range" (#[] ++ #[ .cell dictInt8Signed, intV 8, intV (-200) ])
      (program := #[.dictGetNear 12]) -- [B6][B5]
      ,
    mkCase "ok/int/cond-false-positive" (#[] ++ #[ .cell dictInt8Unsigned, intV 8, intV (-1) ])
      (program := #[.dictGetNear 8]) -- [B6]
      ,
    mkCase "ok/int/hit-signed-eq" (#[] ++ #[ .cell dictInt8Signed, intV 8, intV 1 ])
      (program := #[.dictGetNear 13]) -- [B5]
      ,
    mkCase "ok/int/hit-unsigned-eq" (#[] ++ #[ .cell dictInt8Unsigned, intV 8, intV 1 ])
      (program := #[.dictGetNear 9]) -- [B5]
      ,
    mkCase "ok/int/hit-n257" (#[] ++ #[ .cell dictInt257Signed, intV 257, intV 1 ])
      (program := #[.dictGetNear 13]) -- [B5]
      ,
    mkCase "ok/int/dicterr-nearest" (#[] ++ #[ .cell malformedDict, intV 8, intV 1 ])
      (program := #[.dictGetNear 12]) -- [B7]
      ,
    mkCase "ok/int/dicterr-minmax" (#[] ++ #[ .cell malformedDict, intV 8, intV (-200) ])
      (program := #[.dictGetNear 12]) -- [B7]
      ,
    mkCodeCase "ok/raw/f474" (#[] ++ #[ .cell dictSlice4, intV 4, mkSliceV 4 5 ]) rawF474 -- [B4]
      ,
    mkCodeCase "ok/raw/f475" (#[] ++ #[ .cell dictSlice4, intV 4, mkSliceV 4 5 ]) rawF475 -- [B4]
      ,
    mkCodeCase "ok/raw/f47f" (#[] ++ #[ .cell dictSlice4, intV 4, mkSliceV 4 5 ]) rawF47F -- [B4]
      ,
    mkCodeCase "ok/raw/f47a" (#[] ++ #[ .cell dictInt8Unsigned, intV 8, intV 1 ]) rawF47A -- [B4]
      ,
    mkCodeCase "ok/raw/f47b" (#[] ++ #[ .cell dictInt8Signed, intV 8, intV 1 ]) rawF47B -- [B4]
      ,
    mkCodeCase "err/raw/truncated" (#[] ++ #[ .cell dictSlice4, intV 4, mkSliceV 4 5 ]) rawTruncated8 -- [B4]
      ,
    mkCase "gas/base-miss-exact" (#[] ++ #[ .null, intV 4, mkSliceV 4 0 ])
      (program := #[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (gasLimits := oracleGasLimitsExact baseGas), -- [B8]
    mkCase "gas/base-minus-one-oog" (#[] ++ #[ .null, intV 4, mkSliceV 4 0 ])
      (program := #[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (gasLimits := oracleGasLimitsExact baseGasMinusOne), -- [B8]
    mkCase "gas/slice-hit-exact" (#[] ++ #[ .cell dictSlice4, intV 4, mkSliceV 4 5 ])
      (program := #[.pushInt (.num sliceHitGas), .tonEnvOp .setGasLimit, .dictGetNear 5])
      (gasLimits := oracleGasLimitsExact sliceHitGas), -- [B8]
    mkCase "gas/slice-hit-minus-one-oog" (#[] ++ #[ .cell dictSlice4, intV 4, mkSliceV 4 5 ])
      (program := #[.pushInt (.num sliceHitGasMinusOne), .tonEnvOp .setGasLimit, .dictGetNear 5])
      (gasLimits := oracleGasLimitsExact sliceHitGasMinusOne) -- [B8]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictGetPrevFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTGETPREV
