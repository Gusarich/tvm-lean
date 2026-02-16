import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTGET

/-!
INSTRUCTION: DICTGET

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch.
   - `execInstrDictDictGet` handles only `.dictGet`; all other instructions
     continue via `next`.

2. [B2] Runtime stack arity guard.
   - `checkUnderflow 3` is enforced before any typed/numeric checks.

3. [B3] `n` parsing and range validation (`popNatUpTo 1023`).
   - `.typeChk` for non-int `n`.
   - `.rangeChk` for `.nan`, negative values, or values above `1023`.

4. [B4] Dictionary argument validation (`popMaybeCell`).
   - `.null` is accepted (`none` root means miss).
   - Non-null non-cell values throw `.typeChk`.

5. [B5] Slice-key parsing (`intKey = false` path).
   - If the key slice has at least `n` bits, read exactly `n` bits.
   - If it has fewer than `n`, throw `.cellUnd`.
   - `n = 0` is valid; reads zero bits and can hit an empty-key entry.

6. [B6] Integer-key parsing (`intKey = true` path).
   - `.popIntFinite` enforces type and finiteness:
     - `.typeChk` for non-int.
     - `.intOv` for `.nan`.
   - `dictKeyBits?` can return `none` for out-of-range key:
     - `none` is treated as a dictionary miss and pushes `0` without traversal.
   - Signed and unsigned modes differ on representable key ranges.

7. [B7] Dictionary miss/hit behavior.
   - `none` root or miss in traversal pushes `0`.
   - Hit with by-value mode pushes the value slice and `-1`.

8. [B8] By-ref retrieval (`byRef = true`).
   - Hit is valid only when value has `bitsRemaining = 0` and `refsRemaining = 1`.
   - Malformed payload (`bitsRemaining > 0` or `refsRemaining ≠ 1`) throws `.dictErr`.

9. [B9] Dictionary traversal/structure errors.
   - Malformed nodes can throw `.dictErr` through lookup helpers.

10. [B10] Assembler validation and encoding.
   - Valid encodings:
     - `.dictGet false false false` => `0xf40a`
     - `.dictGet false false true`  => `0xf40b`
     - `.dictGet true false false`  => `0xf40c`
     - `.dictGet true false true`   => `0xf40d`
     - `.dictGet true true false`   => `0xf40e`
     - `.dictGet true true true`    => `0xf40f`
   - `.dictGet false true false` is invalid => `.invOpcode`.

11. [B11] Decoder behavior.
   - `0xf40a..0xf40f` decodes to `.dictGet` with `{intKey,unsigned,byRef}` derived from opcode bits.
   - Adjacent boundary opcodes/truncated bits (e.g. `0xf409`, `0xf410`, `0xf4`) are not accepted.

12. [B12] By-width branches and miss/hit at edge widths.
   - Boundaries for `n = 0` and `n = 1` are explicitly reachable; miss path must remain.

13. [B13] Gas accounting.
   - Base gas appears fixed for this opcode family in the tested model; exact and exact-minus-one
     checks should cover success and out-of-gas failure.

TOTAL BRANCHES: 13

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def dictGetId : InstrId := { name := "DICTGET" }

private def dictGetSlice : Instr := .dictGet false false false
private def dictGetSliceRef : Instr := .dictGet false false true
private def dictGetInt : Instr := .dictGet true false false
private def dictGetIntRef : Instr := .dictGet true false true
private def dictGetUInt : Instr := .dictGet true true false
private def dictGetUIntRef : Instr := .dictGet true true true

private def markerSlice (marker : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits marker 16) #[])

private def dict8Marker5 : Slice := markerSlice 0x51
private def dict8Marker6 : Slice := markerSlice 0x52
private def dict8MarkerN1 : Slice := markerSlice 0x53
private def dict1Marker0 : Slice := markerSlice 0x61
private def dict0Marker0 : Slice := markerSlice 0x62
private def dict8U0 : Slice := markerSlice 0x63
private def dict8U7 : Slice := markerSlice 0x64
private def dict8U255 : Slice := markerSlice 0x65

private def byRefValueCell : Cell := Cell.mkOrdinary (natToBits 0x77 16) #[]
private def byRefLeaf : Slice := Slice.ofCell (Cell.mkOrdinary #[] #[byRefValueCell])
private def byRefMalformedLeaf : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 1 1) #[])
private def byRefValueMarker : Value := .cell byRefValueCell

private def requireBits (label : String) (key : Int) (n : Nat) (unsigned : Bool) : BitString :=
  match dictKeyBits? key n unsigned with
  | some bits => bits
  | none => panic! s!"{label}: unsupported key {key} for n={n} unsigned={unsigned}"

private def mkDictFromBitPairs (label : String) (pairs : Array (BitString × Slice)) : Cell :=
  let rootOpt : Option Cell :=
    pairs.foldl
      (fun st pair =>
        match st with
        | some root =>
            let key := pair.1
            let value := pair.2
            match dictSetSliceWithCells (some root) key value .set with
            | .ok (some next, _, _, _) => some next
            | _ => none
        | none =>
            let key := pair.1
            let value := pair.2
            match dictSetSliceWithCells none key value .set with
            | .ok (some root, _, _, _) => some root
            | _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to build dictionary from bit keys"

private def mkDictFromPairs (label : String) (n : Nat) (unsigned : Bool) (pairs : Array (Int × Slice)) : Cell :=
  let rootOpt : Option Cell :=
    pairs.foldl
      (fun st pair =>
        let key := pair.1
        let value := pair.2
        let bits := requireBits label key n unsigned
        match st with
        | some root =>
            match dictSetSliceWithCells (some root) bits value .set with
            | .ok (some next, _, _, _) => some next
            | _ => none
        | none =>
            match dictSetSliceWithCells none bits value .set with
            | .ok (some root, _, _, _) => some root
            | _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to build dictionary"

private def dictSlice8Root : Cell :=
  mkDictFromBitPairs "dictSlice8Root" #[
    (natToBits 5 8, dict8Marker5),
    (natToBits 6 8, dict8Marker6),
    (natToBits 255 8, dict8MarkerN1)
  ]

private def dictSlice1Root : Cell :=
  mkDictFromBitPairs "dictSlice1Root" #[
    (natToBits 0 1, dict1Marker0),
    (natToBits 1 1, dict8Marker5)
  ]

private def dictSlice0Root : Cell :=
  mkDictFromBitPairs "dictSlice0Root" #[
    (#[], dict0Marker0)
  ]

private def dictSliceByRefRoot : Cell :=
  mkDictFromBitPairs "dictSliceByRefRoot" #[
    (natToBits 5 8, byRefLeaf),
    (natToBits 1 8, byRefMalformedLeaf),
    (natToBits 8 8, byRefMalformedLeaf)
  ]

private def dictInt8Root : Cell :=
  mkDictFromPairs "dictInt8Root" 8 false #[
    (5, dict8Marker5),
    (6, dict8Marker6),
    (-1, dict8MarkerN1)
  ]

private def dictInt1Root : Cell :=
  mkDictFromPairs "dictInt1Root" 1 false #[(0, dict1Marker0)]

private def dictInt0Root : Cell :=
  mkDictFromPairs "dictInt0Root" 0 false #[(0, dict0Marker0)]

private def dictInt8UnsignedRoot : Cell :=
  mkDictFromPairs "dictInt8UnsignedRoot" 8 true #[
    (0, dict8U0),
    (7, dict8U7),
    (255, dict8U255)
  ]

private def dictInt8ByRefRoot : Cell :=
  mkDictFromPairs "dictInt8ByRefRoot" 8 false #[
    (5, byRefLeaf),
    (1, byRefMalformedLeaf)
  ]

private def dictIntUnsignedByRefRoot : Cell :=
  mkDictFromPairs "dictIntUnsignedByRefRoot" 8 true #[
    (0, byRefLeaf),
    (255, byRefMalformedLeaf)
  ]

private def malformedDictCell : Cell := Cell.mkOrdinary (natToBits 0b10 2) #[]

private def dictGetSliceGas : Int := computeExactGasBudget dictGetSlice
private def dictGetSliceGasMinusOne : Int := computeExactGasBudgetMinusOne dictGetSlice
private def dictGetIntGas : Int := computeExactGasBudget dictGetInt
private def dictGetIntGasMinusOne : Int := computeExactGasBudgetMinusOne dictGetInt

private def dictGetUIntGas : Int := computeExactGasBudget dictGetUInt
private def dictGetUIntGasMinusOne : Int := computeExactGasBudgetMinusOne dictGetUInt

private def rawF40a : Cell := Cell.mkOrdinary (natToBits 0xf40a 16) #[]
private def rawF40b : Cell := Cell.mkOrdinary (natToBits 0xf40b 16) #[]
private def rawF40c : Cell := Cell.mkOrdinary (natToBits 0xf40c 16) #[]
private def rawF40d : Cell := Cell.mkOrdinary (natToBits 0xf40d 16) #[]
private def rawF40e : Cell := Cell.mkOrdinary (natToBits 0xf40e 16) #[]
private def rawF40f : Cell := Cell.mkOrdinary (natToBits 0xf40f 16) #[]
private def rawF409 : Cell := Cell.mkOrdinary (natToBits 0xf409 16) #[]
private def rawF410 : Cell := Cell.mkOrdinary (natToBits 0xf410 16) #[]
private def rawF4 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def opcodeSlice16 (w : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits w 16) #[])

private def expectDecodeInvOpcode (label : String) (w : Nat) : IO Unit := do
  match decodeCp0WithBits (opcodeSlice16 w) with
  | .ok (_, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode for {w}, but decode succeeded")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode for {w}, got {reprStr e}")

private def assembleInvOpcode (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok c =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr c}")
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected invOpcode, got {reprStr e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[dictGetSlice])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictGetId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private instance : Coe Instr (Array Instr) where
  coe i := #[i]

private def mkCaseCode
    (name : String)
    (stack : Array Value := #[])
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := dictGetId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictGet
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGet instr stack

private def runDictGetDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGet instr (VM.push (intV 12_345)) stack

private def stackSlice
    (keyBits : BitString)
    (dictValue : Value)
    (n : Int) : Array Value :=
  #[.slice (mkSliceFromBits keyBits), dictValue, intV n]

private def stackInt
    (key : Int)
    (dictValue : Value)
    (n : Int) : Array Value :=
  #[intV key, dictValue, intV n]

private def genDictGetFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (tag, rng2) := randNat rng1 0 999_999
  let baseName := s!"fuzz/{tag}/{shape}"
  let case0 :=
    if shape = 0 then
      mkCase (s!"{baseName}/slice-hit-5") (stackSlice (natToBits 5 8) (.cell dictSlice8Root) 8)
    else if shape = 1 then
      mkCase (s!"{baseName}/slice-hit-6") (stackSlice (natToBits 6 8) (.cell dictSlice8Root) 8)
    else if shape = 2 then
      mkCase (s!"{baseName}/slice-miss") (stackSlice (natToBits 7 8) (.cell dictSlice8Root) 8)
    else if shape = 3 then
      mkCase (s!"{baseName}/slice-none-root") (stackSlice (natToBits 5 8) .null 8)
    else if shape = 4 then
      mkCase (s!"{baseName}/slice-too-short") (stackSlice (natToBits 5 4) (.cell dictSlice8Root) 8)
    else if shape = 5 then
      mkCase (s!"{baseName}/slice-key-type-error") (#[.null, .cell dictSlice8Root, intV 8])
    else if shape = 6 then
      mkCase (s!"{baseName}/slice-dict-type-error") (stackSlice (natToBits 5 8) (.builder Builder.empty) 8)
    else if shape = 7 then
      mkCase (s!"{baseName}/int-hit-5") (stackInt 5 (.cell dictInt8Root) 8) dictGetInt
    else if shape = 8 then
      mkCase (s!"{baseName}/int-hit-6") (stackInt 6 (.cell dictInt8Root) 8) dictGetInt
    else if shape = 9 then
      mkCase (s!"{baseName}/int-hit-neg1") (stackInt (-1) (.cell dictInt8Root) 8) dictGetInt
    else if shape = 10 then
      mkCase (s!"{baseName}/int-miss-7") (stackInt 7 (.cell dictInt8Root) 8) dictGetInt
    else if shape = 11 then
      mkCase (s!"{baseName}/int-signed-oob-pos") (stackInt 128 (.cell dictInt8Root) 8) dictGetInt
    else if shape = 12 then
      mkCase (s!"{baseName}/int-signed-oob-neg") (stackInt (-129) (.cell dictInt8Root) 8) dictGetInt
    else if shape = 13 then
      mkCase (s!"{baseName}/int-unsigned-hit") (stackInt 255 (.cell dictInt8UnsignedRoot) 8) dictGetUInt
    else if shape = 14 then
      mkCase (s!"{baseName}/int-unsigned-miss") (stackInt 254 (.cell dictInt8UnsignedRoot) 8) dictGetUInt
    else if shape = 15 then
      mkCase (s!"{baseName}/int-unsigned-oob-neg") (stackInt (-1) (.cell dictInt8UnsignedRoot) 8) dictGetUInt
    else if shape = 16 then
      mkCase (s!"{baseName}/int-unsigned-oob-wide") (stackInt 256 (.cell dictInt8UnsignedRoot) 8) dictGetUInt
    else if shape = 17 then
      mkCase (s!"{baseName}/key-nan") (#[.int .nan, .cell dictInt8Root, intV 8]) dictGetInt
    else if shape = 18 then
      mkCase (s!"{baseName}/key-type-slice") (stackSlice (natToBits 5 8) (.cell dictInt8Root) 8) dictGetInt
    else if shape = 19 then
      mkCase (s!"{baseName}/bad-n-negative") (stackInt 5 (.cell dictInt8Root) (-1)) dictGetInt
    else if shape = 20 then
      mkCase (s!"{baseName}/bad-n-over") (stackInt 5 (.cell dictInt8Root) 1024) dictGetInt
    else if shape = 21 then
      mkCase (s!"{baseName}/byref-slice-hit") (stackSlice (natToBits 5 8) (.cell dictSliceByRefRoot) 8) dictGetSliceRef
    else if shape = 22 then
      mkCase (s!"{baseName}/byref-slice-malformed") (stackSlice (natToBits 1 8) (.cell dictSliceByRefRoot) 8) dictGetSliceRef
    else if shape = 23 then
      mkCase (s!"{baseName}/byref-int-hit") (stackInt 5 (.cell dictInt8ByRefRoot) 8) dictGetIntRef
    else if shape = 24 then
      mkCase (s!"{baseName}/byref-int-malformed") (stackInt 1 (.cell dictInt8ByRefRoot) 8) dictGetIntRef
    else
      mkCaseCode (s!"{baseName}/raw") #[] rawF40a
  ({ case0 with name := s!"{baseName}/{shape}"}, rng2)

def suite : InstrSuite where
  id := dictGetId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        let sentinel : Int := 12_345
        expectOkStack
          "fallback/non-match"
          (runDictGetDispatchFallback .add #[])
          (#[intV sentinel])
        match runDictGet dictGetSlice (stackSlice (natToBits 5 8) (.cell dictSlice8Root) 8) with
        | .ok #[.slice _, .int (.num (-1))] => pure ()
        | .ok st =>
            throw (IO.userError s!"match/executes-dictget: expected [slice,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"match/executes-dictget: expected success, got error {e}") },
    { name := "unit/underflow"
      run := do
        expectErr "empty-stack" (runDictGet dictGetSlice #[]) .stkUnd
        expectErr "one-item" (runDictGet dictGetSlice #[.int (.num 8)]) .stkUnd
        expectErr "two-items" (runDictGet dictGetSlice #[.cell dictSlice8Root, intV 5]) .stkUnd },
    { name := "unit/n-operand-type-and-range"
      run := do
        expectErr "n-not-int/slice" (runDictGet dictGetSlice (#[intV 5, .cell dictSlice8Root, .null])) .typeChk
        expectErr "n-not-int/int" (runDictGet dictGetInt (#[intV 5, .cell dictInt8Root, .null])) .typeChk
        expectErr "n-nan" (runDictGet dictGetSlice (#[intV 5, .cell dictSlice8Root, .int .nan])) .rangeChk
        expectErr "n-negative" (runDictGet dictGetSlice (#[intV 5, .cell dictSlice8Root, intV (-1)])) .rangeChk
        expectErr "n-too-large" (runDictGet dictGetSlice (#[intV 5, .cell dictSlice8Root, intV 1024])) .rangeChk },
    { name := "unit/dict-and-key-type-checks"
      run := do
        expectErr "dict-not-null-or-cell/slice" (runDictGet dictGetSlice (#[.slice (mkSliceFromBits (natToBits 5 8)), .tuple #[], intV 8])) .typeChk
        expectErr "dict-not-null-or-cell/int" (runDictGet dictGetInt (#[intV 5, .builder Builder.empty, intV 8])) .typeChk
        expectErr "key-not-slice/slice" (runDictGet dictGetSlice #[.null, .cell dictSlice8Root, intV 8]) .typeChk
        expectErr "key-cell/slice" (runDictGet dictGetSlice #[.cell Cell.empty, .cell dictSlice8Root, intV 8]) .typeChk
        expectErr "key-not-int/int" (runDictGet dictGetInt #[.slice (mkSliceFromBits (natToBits 5 8)), .cell dictInt8Root, intV 8]) .typeChk
        expectErr "key-nan/int" (runDictGet dictGetInt #[.int .nan, .cell dictInt8Root, intV 8]) .intOv },
    { name := "unit/slice-key-validation"
      run := do
        expectErr "slice-key-too-short"
          (runDictGet dictGetSlice (stackSlice (natToBits 5 4) (.cell dictSlice8Root) 8))
          .cellUnd
        match runDictGet dictGetSlice (stackSlice (natToBits 5 8) (.cell dictSlice0Root) 0) with
        | .ok #[.slice _, .int (.num (-1))] => pure ()
        | .ok st =>
            throw (IO.userError s!"slice-key-n0-hit: expected [slice,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"slice-key-n0-hit: expected success, got error {e}")
        expectOkStack
          "slice-key-n0-miss-root"
          (runDictGet dictGetSlice (stackSlice (natToBits 5 8) .null 0))
          (#[intV 0]) },
    { name := "unit/int-key-miss-hit"
      run := do
        match runDictGet dictGetInt (stackInt 5 (.cell dictInt8Root) 8) with
        | .ok #[.slice _, .int (.num (-1))] => pure ()
        | .ok st =>
            throw (IO.userError s!"signed-hit-5: expected [slice,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"signed-hit-5: expected success, got error {e}")
        expectOkStack
          "signed-miss-positive"
          (runDictGet dictGetInt (stackInt 127 (.cell dictInt8Root) 8))
          (#[intV 0])
        match runDictGet dictGetUInt (stackInt 255 (.cell dictInt8UnsignedRoot) 8) with
        | .ok #[.slice _, .int (.num (-1))] => pure ()
        | .ok st =>
            throw (IO.userError s!"unsigned-hit-255: expected [slice,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"unsigned-hit-255: expected success, got error {e}")
        expectOkStack
          "unsigned-miss-negative"
          (runDictGet dictGetUInt (stackInt (-1) (.cell dictInt8UnsignedRoot) 8))
          (#[intV 0])
        expectOkStack
          "signed-key-width"
          (runDictGet dictGetInt (stackInt 1 (.cell dictInt1Root) 1))
          (#[intV 0])
        expectOkStack
          "unsigned-key-width"
          (runDictGet dictGetUInt (stackInt 1 (.cell dictInt0Root) 0))
          (#[intV 0]) },
    { name := "unit/stack-preserve"
      run := do
        match runDictGet dictGetSlice #[intV 77, .slice (mkSliceFromBits (natToBits 5 8)), .cell dictSlice8Root, intV 8] with
        | .ok #[.int (.num 77), .slice _, .int (.num (-1))] => pure ()
        | .ok st =>
            throw (IO.userError s!"slice-preserve-prefix: expected [77,slice,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"slice-preserve-prefix: expected success, got error {e}")
        match runDictGet dictGetInt #[intV 77, intV 5, .cell dictInt8Root, intV 8] with
        | .ok #[.int (.num 77), .slice _, .int (.num (-1))] => pure ()
        | .ok st =>
            throw (IO.userError s!"int-preserve-prefix: expected [77,slice,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"int-preserve-prefix: expected success, got error {e}") },
    { name := "unit/by-ref-retrieval"
      run := do
        expectOkStack
          "slice-byref-hit"
          (runDictGet dictGetSliceRef (stackSlice (natToBits 5 8) (.cell dictSliceByRefRoot) 8))
          (#[byRefValueMarker, intV (-1)])
        expectErr
          "slice-byref-malformed"
          (runDictGet dictGetSliceRef (stackSlice (natToBits 1 8) (.cell dictSliceByRefRoot) 8))
          .dictErr
        expectOkStack
          "int-byref-hit"
          (runDictGet dictGetIntRef (stackInt 5 (.cell dictInt8ByRefRoot) 8))
          (#[byRefValueMarker, intV (-1)])
        expectErr
          "int-byref-malformed"
          (runDictGet dictGetIntRef (stackInt 1 (.cell dictInt8ByRefRoot) 8))
          .dictErr },
    { name := "unit/malformed-dicts"
      run := do
        match runDictGet dictGetSlice (stackSlice (natToBits 5 8) (.cell malformedDictCell) 8) with
        | .error .dictErr => pure ()
        | .error .cellUnd => pure ()
        | .error e =>
            throw (IO.userError s!"malformed-root-slice: expected dictErr/cellUnd, got {e}")
        | .ok st =>
            throw (IO.userError s!"malformed-root-slice: expected failure, got {reprStr st}")
        match runDictGet dictGetInt (stackInt 5 (.cell malformedDictCell) 8) with
        | .error .dictErr => pure ()
        | .error .cellUnd => pure ()
        | .error e =>
            throw (IO.userError s!"malformed-root-int: expected dictErr/cellUnd, got {e}")
        | .ok st =>
            throw (IO.userError s!"malformed-root-int: expected failure, got {reprStr st}") },
    { name := "unit/asm-encode-paths"
      run := do
        match assembleCp0 [dictGetSlice] with
        | .ok c =>
            if c.bits != natToBits 0xf40a 16 then
              throw (IO.userError s!"encode/dictget expected 0xf40a, got {c.bits.size}")
        | .error e =>
            throw (IO.userError s!"encode/dictget expected success, got {e}")
        match assembleCp0 [dictGetSliceRef] with
        | .ok c =>
            if c.bits != natToBits 0xf40b 16 then
              throw (IO.userError s!"encode/dictget-ref expected 0xf40b, got {c.bits.size}")
        | .error e =>
            throw (IO.userError s!"encode/dictget-ref expected success, got {e}")
        match assembleCp0 [dictGetInt] with
        | .ok c =>
            if c.bits != natToBits 0xf40c 16 then
              throw (IO.userError s!"encode/dictiget expected 0xf40c, got {c.bits.size}")
        | .error e =>
            throw (IO.userError s!"encode/dictiget expected success, got {e}")
        match assembleCp0 [dictGetIntRef] with
        | .ok c =>
            if c.bits != natToBits 0xf40d 16 then
              throw (IO.userError s!"encode/dictiget-ref expected 0xf40d, got {c.bits.size}")
        | .error e =>
            throw (IO.userError s!"encode/dictiget-ref expected success, got {e}")
        match assembleCp0 [dictGetUInt] with
        | .ok c =>
            if c.bits != natToBits 0xf40e 16 then
              throw (IO.userError s!"encode/dictuget expected 0xf40e, got {c.bits.size}")
        | .error e =>
            throw (IO.userError s!"encode/dictuget expected success, got {e}")
        match assembleCp0 [dictGetUIntRef] with
        | .ok c =>
            if c.bits != natToBits 0xf40f 16 then
              throw (IO.userError s!"encode/dictuget-ref expected 0xf40f, got {c.bits.size}")
        | .error e =>
            throw (IO.userError s!"encode/dictuget-ref expected success, got {e}")
        assembleInvOpcode "invalid-false-unsigned" (.dictGet false true false) },
    { name := "unit/decode-paths"
      run := do
        let s0 := opcodeSlice16 0xf40a
        let _ ← expectDecodeStep "decode/0xf40a" s0 (.dictGet false false false) 16
        let s1 := opcodeSlice16 0xf40b
        let _ ← expectDecodeStep "decode/0xf40b" s1 (.dictGet false false true) 16
        let s2 := opcodeSlice16 0xf40c
        let _ ← expectDecodeStep "decode/0xf40c" s2 (.dictGet true false false) 16
        let s3 := opcodeSlice16 0xf40d
        let _ ← expectDecodeStep "decode/0xf40d" s3 (.dictGet true false true) 16
        let s4 := opcodeSlice16 0xf40e
        let _ ← expectDecodeStep "decode/0xf40e" s4 (.dictGet true true false) 16
        let s5 := opcodeSlice16 0xf40f
        let _ ← expectDecodeStep "decode/0xf40f" s5 (.dictGet true true true) 16
        expectDecodeInvOpcode "decode/0xf409" 0xf409
        expectDecodeInvOpcode "decode/0xf410" 0xf410
        match decodeCp0WithBits (Slice.ofCell rawF4) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode/truncated/8-bit expected failure") }
  ]
  oracle := #[
    -- [B2][B3]
    mkCase "err/underflow-empty" #[],
    mkCase "err/underflow-one" #[.int (.num 8)],
    mkCase "err/underflow-two" #[.cell dictSlice8Root, intV 5],

    -- [B3]
    mkCase "err/n-not-int/slice" #[intV 5, .cell dictSlice8Root, .null],
    mkCase "err/n-nan" #[intV 5, .cell dictSlice8Root] #[.pushInt .nan, dictGetSlice],
    mkCase "err/n-negative" #[intV 5, .cell dictSlice8Root, intV (-1)],
    mkCase "err/n-too-large" #[intV 5, .cell dictSlice8Root, intV 1024],
    mkCase "err/n-not-int/int" #[intV 5, .cell dictInt8Root, .builder Builder.empty],

    -- [B4]
    mkCase "err/dict-not-cell/slice" (#[intV 5, .int (.num 7), intV 8]) dictGetSlice,
    mkCase "err/dict-not-cell/int" (#[intV 5, .tuple #[], intV 8]) dictGetInt,

    -- [B5]
    mkCase "err/key-not-slice/slice" (#[.null, .cell dictSlice8Root, intV 8]) dictGetSlice,
    mkCase "err/key-cell/slice" (#[.cell Cell.empty, .cell dictSlice8Root, intV 8]) dictGetSlice,
    mkCase "err/key-too-short/slice" (stackSlice (natToBits 5 4) (.cell dictSlice8Root) 8),
    mkCase "err/key-not-int/int" (stackSlice (natToBits 5 8) (.cell dictInt8Root) 8) dictGetInt,
    mkCase "err/key-nan/int"
      (#[.cell dictInt8Root, intV 8])
      #[.pushInt .nan, .xchg0 1, .xchg 1 2, dictGetInt],

    -- [B6]
    mkCase "ok/signed-miss-out-of-range-pos" (stackInt 128 (.cell dictInt8Root) 8) dictGetInt,
    mkCase "ok/signed-miss-out-of-range-neg" (stackInt (-129) (.cell dictInt8Root) 8) dictGetInt,
    mkCase "ok/unsigned-miss-out-of-range-pos" (stackInt 256 (.cell dictInt8UnsignedRoot) 8) dictGetUInt,
    mkCase "ok/unsigned-miss-negative" (stackInt (-1) (.cell dictInt8UnsignedRoot) 8) dictGetUInt,
    mkCase "ok/signed-n1-miss" (stackInt 1 (.cell dictInt1Root) 1) dictGetInt,
    mkCase "ok/unsigned-n0-miss" (stackInt 1 (.cell dictInt0Root) 0) dictGetUInt,

    -- [B7][B13]
    mkCase "ok/slice-hit-5" (stackSlice (natToBits 5 8) (.cell dictSlice8Root) 8),
    mkCase "ok/slice-hit-6" (stackSlice (natToBits 6 8) (.cell dictSlice8Root) 8),
    mkCase "ok/slice-miss" (stackSlice (natToBits 7 8) (.cell dictSlice8Root) 8),
    mkCase "ok/slice-none-root" (stackSlice (natToBits 5 8) .null 8),
    mkCase "ok/slice-n0-hit" (stackSlice (natToBits 0 0) (.cell dictSlice0Root) 0),
    mkCase "ok/int-hit-5" (stackInt 5 (.cell dictInt8Root) 8) dictGetInt,
    mkCase "ok/int-hit-neg1" (stackInt (-1) (.cell dictInt8Root) 8) dictGetInt,
    mkCase "ok/int-hit-255-unsigned" (stackInt 255 (.cell dictInt8UnsignedRoot) 8) dictGetUInt,
    mkCase "ok/int-miss-8-unsigned" (stackInt 8 (.cell dictInt8UnsignedRoot) 8) dictGetUInt,

    -- [B8]
    mkCase "ok/slice-byref-hit" (stackSlice (natToBits 5 8) (.cell dictSliceByRefRoot) 8) dictGetSliceRef,
    mkCase "err/slice-byref-malformed" (stackSlice (natToBits 1 8) (.cell dictSliceByRefRoot) 8) dictGetSliceRef,
    mkCase "ok/int-byref-hit" (stackInt 5 (.cell dictInt8ByRefRoot) 8) dictGetIntRef,
    mkCase "err/int-byref-malformed" (stackInt 1 (.cell dictInt8ByRefRoot) 8) dictGetIntRef,
    mkCase "ok/uint-byref-hit" (stackInt 0 (.cell dictIntUnsignedByRefRoot) 8) dictGetUIntRef,
    mkCase "err/uint-byref-malformed" (stackInt 255 (.cell dictIntUnsignedByRefRoot) 8) dictGetUIntRef,

    -- [B9]
    mkCase "err/malformed-root-slice" (stackInt 5 (.cell malformedDictCell) 8) dictGetSlice,
    mkCase "err/malformed-root-int" (stackInt 5 (.cell malformedDictCell) 8) dictGetInt,
    mkCase "err/malformed-root-uint" (stackInt 5 (.cell malformedDictCell) 8) dictGetUInt,

    -- [B10]
    mkCaseCode "raw/decode/f40a" #[] rawF40a,
    mkCaseCode "raw/decode/f40b" #[] rawF40b,
    mkCaseCode "raw/decode/f40c" #[] rawF40c,
    mkCaseCode "raw/decode/f40d" #[] rawF40d,
    mkCaseCode "raw/decode/f40e" #[] rawF40e,
    mkCaseCode "raw/decode/f40f" #[] rawF40f,
    mkCaseCode "raw/decode/f409" #[] rawF409,
    mkCaseCode "raw/decode/f410" #[] rawF410,
    mkCaseCode "raw/decode/truncated" #[] rawF4,

    -- [B13]
    mkCase "gas/exact-slice"
      (stackSlice (natToBits 5 8) (.cell dictSlice8Root) 8)
      (#[.pushInt (.num dictGetSliceGas), .tonEnvOp .setGasLimit, dictGetSlice])
      (oracleGasLimitsExact dictGetSliceGas),
    mkCase "gas/exact-minus-one-slice"
      (stackSlice (natToBits 5 8) (.cell dictSlice8Root) 8)
      (#[.pushInt (.num dictGetSliceGasMinusOne), .tonEnvOp .setGasLimit, dictGetSlice])
      (oracleGasLimitsExactMinusOne dictGetSliceGasMinusOne),
    mkCase "gas/exact-int"
      (stackInt 5 (.cell dictInt8Root) 8)
      (#[.pushInt (.num dictGetIntGas), .tonEnvOp .setGasLimit, dictGetInt])
      (oracleGasLimitsExact dictGetIntGas),
    mkCase "gas/exact-minus-one-int"
      (stackInt 5 (.cell dictInt8Root) 8)
      (#[.pushInt (.num dictGetIntGasMinusOne), .tonEnvOp .setGasLimit, dictGetInt])
      (oracleGasLimitsExactMinusOne dictGetIntGasMinusOne),
    mkCase "gas/exact-uint"
      (stackInt 255 (.cell dictInt8UnsignedRoot) 8)
      (#[.pushInt (.num dictGetUIntGas), .tonEnvOp .setGasLimit, dictGetUInt])
      (oracleGasLimitsExact dictGetUIntGas)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictGetId
      count := 500
      gen := genDictGetFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTGET
