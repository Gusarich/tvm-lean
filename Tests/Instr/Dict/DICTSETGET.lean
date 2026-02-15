import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTSETGET

/-!
INSTRUCTION: DICTSETGET

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch path:
   - `.dictExt (.mutGet false false false .set)` is handled only by
     `execInstrDictExt`; non-`dictExt` opcodes fall through to `next`.

2. [B2] Runtime arity checks:
   - `checkUnderflow 4` must reject stacks with fewer than 4 items.

3. [B3] Runtime `n` validation:
   - `popNatUpTo 1023` accepts `n <= 1023`.
   - Negative, NaN, and larger than 1023 values all raise `.rangeChk`.

4. [B4] Runtime argument typing:
   - `popMaybeCell` accepts `null` and `.cell` dictionary roots; other values raise `.typeChk`.
   - Key must be a slice (type check before key-size checks).
   - Value must be a slice (type check before key-mutation attempts).

5. [B5] Runtime key extraction:
   - For non-int keys the branch `haveBits n` is required.
   - Insufficient key bits (e.g. n=4 with a 3-bit key slice) raise `.cellUnd`.
   - `n = 0` is valid when key bits are present (or any empty slice).

6. [B6] Runtime miss branch:
   - If key absent (from `null` or non-empty dict without key), result is `(D', 0)` with new root.

7. [B7] Runtime hit branch:
   - If key is present, old value is returned as a slice and status is `-1`.
   - The dictionary root is updated to reflect `set` semantics.

8. [B8] Runtime malformed payload/root branch:
   - Malformed dictionary roots are rejected via `.dictErr`.

9. [B9] Assembler constraints:
   - `Asm/Cp0` encodes `.dictExt (.mutGet false false false .set)` (opcode `0xf41a`).

10. [B10] Decoder boundaries and adjacency:
    - `0xf41a` decodes to `.dictExt (.mutGet false false false .set)`.
    - Adjacent values `0xf41b..0xf41f` decode to REF/INT/UNSIGNED variants.
    - `0xf4` truncated opcode decodes as `.invOpcode`.
    - `0xf419` is the previous opcode gap and must decode as `.invOpcode`.

11. [B11] Gas accounting:
    - Base instruction gas from 16-bit decode is fixed (`computeExactGasBudget instr = 26`).
    - `set` branches that miss can also create new dictionary cells; these are
      accounted via `cellCreateGasPrice * created`.
    - Exact-gas and exact-minus-one cases are tested on both hit and insertion paths.

TOTAL BRANCHES: 11

Every oracle test below is tagged with the branch(es) it covers.
Runtime branches that are hard to hit deterministically are targeted by the fuzzer.
-/

private def suiteId : InstrId := { name := "DICTSETGET" }

private def instr : Instr := .dictExt (.mutGet false false false .set)

private def raw16 (w : Nat) : Cell := Cell.mkOrdinary (natToBits w 16) #[]

private def rawOpcode : Cell := raw16 0xf41a
private def rawOpcodeRef : Cell := raw16 0xf41b
private def rawOpcodeInt : Cell := raw16 0xf41c
private def rawOpcodeIntRef : Cell := raw16 0xf41d
private def rawOpcodeUnsigned : Cell := raw16 0xf41e
private def rawOpcodeUnsignedRef : Cell := raw16 0xf41f
private def rawOpcodeGap : Cell := raw16 0xf419
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]

private def valueA : Slice := mkSliceFromBits (natToBits 0xA5 8)
private def valueB : Slice := mkSliceFromBits (natToBits 0x3C 8)
private def valueC : Slice := mkSliceFromBits (natToBits 0x6E 8)
private def valueD : Slice := mkSliceFromBits (natToBits 0x77 8)
private def valueE : Slice := mkSliceFromBits (natToBits 0x00 8)

private def key4A : BitString := natToBits 0xA 4
private def key4B : BitString := natToBits 0xB 4
private def key4C : BitString := natToBits 0xC 4
private def key4D : BitString := natToBits 0xD 4
private def key8A : BitString := natToBits 0xA5 8
private def key8B : BitString := natToBits 0x5A 8
private def key8C : BitString := natToBits 0x3F 8
private def key1 : Slice := mkSliceFromBits (natToBits 0x1 1)
private def key3 : Slice := mkSliceFromBits (natToBits 0x7 3)
private def key4 : Slice := mkSliceFromBits (natToBits 0xA 4)
private def key4b : Slice := mkSliceFromBits (natToBits 0xB 4)
private def key4c : Slice := mkSliceFromBits (natToBits 0xC 4)
private def key4d : Slice := mkSliceFromBits (natToBits 0xD 4)
private def key8a : Slice := mkSliceFromBits key8A
private def key8b : Slice := mkSliceFromBits key8B
private def key0 : Slice := mkSliceFromBits #[]
private def key1023 : Slice := mkSliceFromBits (Array.replicate 1023 true)
private def keyMalformedShort : Slice := mkSliceFromBits (natToBits 0x8 1)

private def mkDictSliceRoot! (label : String) (pairs : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for pair in pairs do
      let (k, v) := pair
      match dictSetSliceWithCells root k v .set with
      | .ok (some newRoot, _ok, _created, _loaded) =>
          root := some newRoot
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while adding {k}"
      | .error e =>
          panic! s!"{label}: dictSetSliceWithCells failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: no entries were inserted"

private def sliceRemBits (s : Slice) : BitString :=
  s.cell.bits.extract s.bitPos s.cell.bits.size

private def dict4Single : Cell :=
  mkDictSliceRoot! "dict4/single" #[(key4A, valueA)]

private def dict4Pair : Cell :=
  mkDictSliceRoot! "dict4/pair" #[(key4A, valueA), (key4B, valueB)]

private def dict4Triple : Cell :=
  mkDictSliceRoot! "dict4/triple" #[(key4A, valueA), (key4C, valueC), (key4D, valueD)]

private def dict0Single : Cell :=
  mkDictSliceRoot! "dict0/single" #[(#[], valueA)]

private def dict8Single : Cell :=
  mkDictSliceRoot! "dict8/single" #[(key8A, valueB)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b111 3) #[]

private def expectedSetReplace4A : Cell :=
  match dictLookupSetSliceWithCells (some dict4Single) key4A valueE .set with
  | .ok (_, some r, _ok, _created, _loaded) => r
  | .ok (_, none, _, _, _) =>
      panic! "expected dict4Single set replacement to produce a root"
  | .error e =>
      panic! s!"expected dict4Single set replacement failed: {reprStr e}"

private def expectedSetInsert4C : Cell :=
  match dictLookupSetSliceWithCells (some dict4Pair) key4C valueE .set with
  | .ok (_, some r, _ok, _created, _loaded) => r
  | .ok (_, none, _, _, _) =>
      panic! "expected dict4Pair insertion to produce a root"
  | .error e =>
      panic! s!"expected dict4Pair insertion failed: {reprStr e}"

private def expectedSetInsert4D : Cell :=
  match dictLookupSetSliceWithCells (some dict4Pair) key4D valueC .set with
  | .ok (_, some r, _ok, _created, _loaded) => r
  | .ok (_, none, _, _, _) =>
      panic! "expected dict4Pair insertion at 4D to produce a root"
  | .error e =>
      panic! s!"expected dict4Pair insertion at 4D failed: {reprStr e}"

private def expectedSetNull4C : Cell :=
  match dictLookupSetSliceWithCells none key4C valueA .set with
  | .ok (_, some r, _ok, _created, _loaded) => r
  | .ok (_, none, _, _, _) =>
      panic! "expected null set miss to produce a root"
  | .error e =>
      panic! s!"expected null set miss failed: {reprStr e}"

private def expectedSetNull0 : Cell :=
  match dictLookupSetSliceWithCells none (#[] : BitString) valueA .set with
  | .ok (_, some r, _ok, _created, _loaded) => r
  | .ok (_, none, _, _, _) =>
      panic! "expected null set miss for n=0 to produce a root"
  | .error e =>
      panic! s!"expected null set miss for n=0 failed: {reprStr e}"

private def setInsertCreated : Nat :=
  match dictLookupSetSliceWithCells none key4C valueA .set with
  | .ok (_, _, _ok, created, _) => created
  | .error e =>
      panic! s!"failed to compute created cells for null miss insert: {reprStr e}"

private def baseGas : Int := computeExactGasBudget instr

private def baseGasMinusOne : Int := if baseGas > 0 then baseGas - 1 else 0

private def insertGas : Int :=
  baseGas + Int.ofNat setInsertCreated * cellCreateGasPrice

private def insertGasMinusOne : Int := if insertGas > 0 then insertGas - 1 else 0

private def gasBaseExact : OracleGasLimits := oracleGasLimitsExact baseGas

private def gasBaseExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne baseGasMinusOne

private def gasInsertExact : OracleGasLimits :=
  { gasLimit := insertGas, gasMax := insertGas, gasCredit := 0 }

private def gasInsertExactMinusOne : OracleGasLimits :=
  { gasLimit := insertGasMinusOne, gasMax := insertGasMinusOne, gasCredit := 0 }

private def mkGasProgram (gasLimit : Int) : Cell :=
  match assembleCp0 [ .pushInt (.num gasLimit), .tonEnvOp .setGasLimit ] with
  | .ok c =>
      Cell.mkOrdinary (c.bits ++ rawOpcode.bits) #[]
  | .error e =>
      panic! s!"DICTSETGET gas program assembly failed: {reprStr e}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (code : Cell := rawOpcode)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, _, rest) =>
      if instr != expected || rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: unexpected decode result {reprStr instr}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected decode failure {expected}, got {instr}")
  | .error e =>
      if e != expected then
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectAssembleOk16 (label : String) (code : Instr) : IO Unit := do
  match assembleCp0 [code] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")
  | .ok cell =>
      match decodeCp0WithBits (Slice.ofCell cell) with
      | .error e =>
          throw (IO.userError s!"{label}: expected decode success, got {e}")
      | .ok (instr, bits, rest) =>
          if instr != code then
            throw (IO.userError s!"{label}: expected {reprStr code}, got {reprStr instr}")
          else if bits != 16 then
            throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
          else if rest.bitsRemaining + rest.refsRemaining != 0 then
            throw (IO.userError s!"{label}: expected end-of-stream decode")

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt .add (VM.push (intV 909)) stack

private def runDictSetGetDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def genDICTSETGETFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    (mkCase s!"fuzz/ok/hit/4a/{tag}" #[.slice valueB, .slice key4, .cell dict4Single, intV 4], rng2)
  else if shape = 1 then
    (mkCase s!"fuzz/ok/hit/4b/{tag}" #[.slice valueA, .slice key4b, .cell dict4Pair, intV 4], rng2)
  else if shape = 2 then
    (mkCase s!"fuzz/ok/hit/4d/{tag}" #[.slice valueE, .slice key4d, .cell dict4Triple, intV 4], rng2)
  else if shape = 3 then
    (mkCase s!"fuzz/ok/hit/0/{tag}" #[.slice valueC, .slice key0, .cell dict0Single, intV 0], rng2)
  else if shape = 4 then
    (mkCase s!"fuzz/ok/hit/1023/{tag}" #[.slice valueA, .slice key1023, .cell dict4Single, intV 1023], rng2)
  else if shape = 5 then
    (mkCase s!"fuzz/ok/hit/8a/{tag}" #[.slice valueE, .slice key8a, .cell dict8Single, intV 8], rng2)
  else if shape = 6 then
    (mkCase s!"fuzz/ok/miss/null4/{tag}" #[.slice valueD, .slice key4, .null, intV 4], rng2)
  else if shape = 7 then
    (mkCase s!"fuzz/ok/miss/null0/{tag}" #[.slice valueD, .slice key0, .null, intV 0], rng2)
  else if shape = 8 then
    (mkCase s!"fuzz/ok/miss/null8/{tag}" #[.slice valueD, .slice key8b, .null, intV 8], rng2)
  else if shape = 9 then
    (mkCase s!"fuzz/ok/miss/nonempty8/{tag}" #[.slice valueD, .slice key8b, .cell dict8Single, intV 8], rng2)
  else if shape = 10 then
    (mkCase s!"fuzz/ok/miss/nonempty4/{tag}" #[.slice valueC, .slice key4d, .cell dict4Triple, intV 4], rng2)
  else if shape = 11 then
    (mkCase s!"fuzz/ok/miss/n1023/{tag}" #[.slice valueB, .slice key1023, .null, intV 1023], rng2)
  else if shape = 12 then
    (mkCase s!"fuzz/ok/replace-from-pair/{tag}" #[.slice valueD, .slice key4, .cell dict4Pair, intV 4], rng2)
  else if shape = 13 then
    (mkCase s!"fuzz/ok/insert-from-pair/{tag}" #[.slice valueE, .slice key3, .cell dict4Pair, intV 4], rng2)
  else if shape = 14 then
    (mkCase s!"fuzz/err/underflow0/{tag}" #[], rng2)
  else if shape = 15 then
    (mkCase s!"fuzz/err/underflow1/{tag}" #[intV 4], rng2)
  else if shape = 16 then
    (mkCase s!"fuzz/err/underflow2/{tag}" #[.slice key4, .null], rng2)
  else if shape = 17 then
    (mkCase s!"fuzz/err/underflow3/{tag}" #[.slice key4, .slice valueA, .cell dict4Single], rng2)
  else if shape = 18 then
    (mkCase s!"fuzz/err/n-neg/{tag}" #[.slice valueA, .slice key4, .cell dict4Single, intV (-1)], rng2)
  else if shape = 19 then
    (mkCase s!"fuzz/err/n-too-large/{tag}" #[.slice valueA, .slice key4, .cell dict4Single, intV 1024], rng2)
  else if shape = 20 then
    (mkCase s!"fuzz/err/n-nan/{tag}" #[.slice valueA, .slice key4, .cell dict4Single, .int .nan], rng2)
  else if shape = 21 then
    (mkCase s!"fuzz/err/dict-type/{tag}" #[.slice valueA, .slice key4, .tuple #[], intV 4], rng2)
  else if shape = 22 then
    (mkCase s!"fuzz/err/key-type/{tag}" #[.slice valueA, .int (.num 1), .cell dict4Single, intV 4], rng2)
  else if shape = 23 then
    (mkCase s!"fuzz/err/value-type/{tag}" #[.int (.num 0), .slice key4, .cell dict4Single, intV 4], rng2)
  else if shape = 24 then
    (mkCase s!"fuzz/err/key-short/{tag}" #[.slice valueA, .slice key3, .cell dict4Single, intV 4], rng2)
  else if shape = 25 then
    (mkCase s!"fuzz/err/key-short-n1/{tag}" #[.slice valueA, .slice key3, .cell dict4Single, intV 1], rng2)
  else if shape = 26 then
    (mkCase s!"fuzz/err/malformed/{tag}" #[.slice valueA, .slice key4, .cell malformedDict, intV 4], rng2)
  else if shape = 27 then
    (mkCase s!"fuzz/err/malformed-2/{tag}" #[.slice valueD, .slice key4c, .cell malformedDict, intV 4], rng2)
  else if shape = 28 then
    (mkCase s!"fuzz/gas/exact/base-hit/{tag}"
      #[.slice valueA, .slice key4b, .cell dict4Pair, intV 4]
      (mkGasProgram baseGas)
      gasBaseExact, rng2)
  else if shape = 29 then
    (mkCase s!"fuzz/gas/exact-minus-one/base-hit/{tag}"
      #[.slice valueA, .slice key4b, .cell dict4Pair, intV 4]
      (mkGasProgram baseGasMinusOne)
      gasBaseExactMinusOne, rng2)
  else if shape = 30 then
    (mkCase s!"fuzz/gas/exact/insert/{tag}"
      #[.slice valueC, .slice key4c, .null, intV 4]
      (mkGasProgram insertGas)
      gasInsertExact, rng2)
  else if shape = 31 then
    (mkCase s!"fuzz/gas/exact-minus-one/insert/{tag}"
      #[.slice valueC, .slice key4c, .null, intV 4]
      (mkGasProgram insertGasMinusOne)
      gasInsertExactMinusOne, rng2)
  else if shape = 32 then
    (mkCase s!"fuzz/gas/exact/insert0/{tag}"
      #[.slice valueA, .slice key0, .null, intV 0]
      (mkGasProgram baseGas)
      gasBaseExact, rng2)
  else if shape = 33 then
    (mkCase s!"fuzz/gas/exact-minus-one/insert0/{tag}"
      #[.slice valueA, .slice key0, .null, intV 0]
      (mkGasProgram baseGasMinusOne)
      gasBaseExactMinusOne, rng2)
  else if shape = 34 then
    (mkCase s!"fuzz/ok/hit-boundary-1023/{tag}" #[.slice valueB, .slice key1023, .cell dict4Single, intV 1023], rng2)
  else if shape = 35 then
    (mkCase s!"fuzz/ok/miss-key8b-pair/{tag}" #[.slice valueD, .slice key8b, .cell dict4Single, intV 8], rng2)
  else if shape = 36 then
    (mkCase s!"fuzz/ok/replace-to-bigger/{tag}" #[.slice valueB, .slice key4, .cell dict4Triple, intV 4], rng2)
  else if shape = 37 then
    (mkCase s!"fuzz/ok/miss/empty0/{tag}" #[.slice valueE, .slice key0, .cell dict4Single, intV 0], rng2)
  else if shape = 38 then
    (mkCase s!"fuzz/err/type-value-null/{tag}" #[.null, .slice key4, .cell dict4Single, intV 4], rng2)
  else
    (mkCase s!"fuzz/err/type-key-null/{tag}" #[.slice valueA, .null, .cell dict4Single, intV 4], rng2)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        let out := runDispatchFallback #[]
        expectOkStack "unit/dispatch/fallback" out #[intV 909] },
    { name := "unit/decode/self"
      run := do
        expectDecodeOk "unit/decode/self" rawOpcode (.dictExt (.mutGet false false false .set)) },
    { name := "unit/decode/neighbor/ref"
      run := do
        expectDecodeOk "unit/decode/neighbor/ref" rawOpcodeRef (.dictExt (.mutGet false false true .set)) },
    { name := "unit/decode/neighbor/int"
      run := do
        expectDecodeOk "unit/decode/neighbor/int" rawOpcodeInt (.dictExt (.mutGet true false false .set)) },
    { name := "unit/decode/neighbor/unsigned"
      run := do
        expectDecodeOk "unit/decode/neighbor/unsigned" rawOpcodeUnsigned (.dictExt (.mutGet true true false .set)) },
    { name := "unit/decode/ref-unsigned"
      run := do
        expectDecodeOk "unit/decode/ref-unsigned" rawOpcodeUnsignedRef (.dictExt (.mutGet true true true .set)) },
    { name := "unit/decode/gap"
      run := do
        expectDecodeErr "unit/decode/gap" rawOpcodeGap .invOpcode },
    { name := "unit/decode/truncated-8"
      run := do
        expectDecodeErr "unit/decode/truncated-8" rawTruncated8 .invOpcode },
    { name := "unit/assemble/encodes"
      run := do
        expectAssembleOk16 "unit/assemble/encodes" instr },
    { name := "unit/ok/insert-null"
      run := do
        expectOkStack "unit/ok/insert-null"
          (runDictSetGetDirect #[.slice valueA, .slice key4c, .null, intV 4])
          #[.cell expectedSetNull4C, intV 0] },
    { name := "unit/ok/replace-existing"
      run := do
        match runDictSetGetDirect #[.slice valueE, .slice key4, .cell dict4Single, intV 4] with
        | .error e =>
            throw (IO.userError s!"unit/ok/replace-existing: expected ok, got {e}")
        | .ok st =>
            match st with
            | #[.cell root, .slice oldValue, status] =>
                if root != expectedSetReplace4A then
                  throw (IO.userError s!"unit/ok/replace-existing: root mismatch, got {root.bits}")
                if sliceRemBits oldValue != valueA.cell.bits then
                  throw (IO.userError s!"unit/ok/replace-existing: old value mismatch, got {sliceRemBits oldValue}")
                if status != intV (-1) then
                  throw (IO.userError s!"unit/ok/replace-existing: status mismatch, got {reprStr status}")
            | _ =>
                throw (IO.userError s!"unit/ok/replace-existing: unexpected stack {reprStr st}") },
    { name := "unit/ok/replace-non-root"
      run := do
        expectOkStack "unit/ok/replace-non-root"
          (runDictSetGetDirect #[.slice valueE, .slice key4c, .cell dict4Pair, intV 4])
          #[.cell expectedSetInsert4C, intV 0] },
    { name := "unit/ok/miss-nonempty"
      run := do
        expectOkStack "unit/ok/miss-nonempty"
          (runDictSetGetDirect #[.slice valueC, .slice key4d, .cell dict4Pair, intV 4])
          #[.cell expectedSetInsert4D, intV 0] },
    { name := "unit/ok/n0-empty"
      run := do
        expectOkStack "unit/ok/n0-empty"
          (runDictSetGetDirect #[.slice valueA, .slice key0, .null, intV 0])
          #[.cell expectedSetNull0, intV 0] },
    { name := "unit/err/underflow-0"
      run := do
        expectErr "unit/err/underflow-0" (runDictSetGetDirect #[]) .stkUnd },
    { name := "unit/err/underflow-1"
      run := do
        expectErr "unit/err/underflow-1" (runDictSetGetDirect #[intV 4]) .stkUnd },
    { name := "unit/err/underflow-2"
      run := do
        expectErr "unit/err/underflow-2" (runDictSetGetDirect #[.slice valueA, .null]) .stkUnd },
    { name := "unit/err/underflow-3"
      run := do
        expectErr "unit/err/underflow-3" (runDictSetGetDirect #[.slice valueA, .slice key4, .cell dict4Single]) .stkUnd },
    { name := "unit/err/n-neg"
      run := do
        expectErr "unit/err/n-neg" (runDictSetGetDirect #[.slice valueA, .slice key4, .cell dict4Single, intV (-1)]) .rangeChk },
    { name := "unit/err/n-too-large"
      run := do
        expectErr "unit/err/n-too-large" (runDictSetGetDirect #[.slice valueA, .slice key4, .cell dict4Single, intV 1024]) .rangeChk },
    { name := "unit/err/n-nan"
      run := do
        expectErr "unit/err/n-nan" (runDictSetGetDirect #[.slice valueA, .slice key4, .cell dict4Single, .int .nan]) .rangeChk },
    { name := "unit/err/dict-type"
      run := do
        expectErr "unit/err/dict-type" (runDictSetGetDirect #[.slice valueA, .slice key4, .tuple #[], intV 4]) .typeChk },
    { name := "unit/err/key-type"
      run := do
        expectErr "unit/err/key-type" (runDictSetGetDirect #[.slice valueA, .int (.num 0), .cell dict4Single, intV 4]) .typeChk },
    { name := "unit/err/value-type"
      run := do
        expectErr "unit/err/value-type" (runDictSetGetDirect #[.int (.num 0), .slice key4, .cell dict4Single, intV 4]) .typeChk },
    { name := "unit/err/key-short"
      run := do
        expectErr "unit/err/key-short" (runDictSetGetDirect #[.slice valueA, .slice key3, .cell dict4Single, intV 4]) .cellUnd },
    { name := "unit/err/key-short-n1"
      run := do
        expectErr "unit/err/key-short-n1" (runDictSetGetDirect #[.slice valueA, .slice key0, .null, intV 1]) .cellUnd },
    { name := "unit/err/malformed-root"
      run := do
        expectErr "unit/err/malformed-root" (runDictSetGetDirect #[.slice valueA, .slice key4, .cell malformedDict, intV 4]) .cellUnd }
  ]
  oracle := #[
    mkCase "ok/miss/null/4-a" #[.slice valueA, .slice key4, .null, intV 4], -- [B6]
    mkCase "ok/miss/null/4-c" #[.slice valueA, .slice key4c, .null, intV 4], -- [B6]
    mkCase "ok/miss/null/0" #[.slice valueA, .slice key0, .null, intV 0], -- [B6][B5]
    mkCase "ok/miss/null/1023" #[.slice valueA, .slice key1023, .null, intV 1023], -- [B6][B5]
    mkCase "ok/miss/nonempty/4" #[.slice valueA, .slice key4c, .cell dict4Single, intV 4], -- [B6]
    mkCase "ok/miss/nonempty/8" #[.slice valueA, .slice key8a, .cell dict8Single, intV 8], -- [B6]
    mkCase "ok/miss/nonempty/0" #[.slice valueD, .slice key0, .cell dict8Single, intV 0], -- [B6][B5]
    mkCase "ok/miss/nonempty/1023" #[.slice valueD, .slice key1023, .cell dict8Single, intV 1023], -- [B6]
    mkCase "ok/hit/single" #[.slice valueB, .slice key4, .cell dict4Single, intV 4], -- [B7]
    mkCase "ok/hit/pair-a" #[.slice valueB, .slice key4, .cell dict4Pair, intV 4], -- [B7]
    mkCase "ok/hit/pair-b" #[.slice valueD, .slice key4b, .cell dict4Pair, intV 4], -- [B7]
    mkCase "ok/hit/triple" #[.slice valueE, .slice key4d, .cell dict4Triple, intV 4], -- [B7]
    mkCase "ok/hit/n0" #[.slice valueC, .slice key0, .cell dict0Single, intV 0], -- [B7][B5]
    mkCase "ok/hit/8" #[.slice valueC, .slice key8a, .cell dict8Single, intV 8], -- [B7]
    mkCase "ok/hit/boundary-edge" #[.slice valueD, .slice key4, .cell dict4Single, intV 4], -- [B7]
    mkCase "err/underflow-0" #[], -- [B2]
    mkCase "err/underflow-1" #[intV 4], -- [B2]
    mkCase "err/underflow-2" #[.slice key4, .null], -- [B2]
    mkCase "err/underflow-3" #[.slice key4, .slice valueA, .cell dict4Single], -- [B2]
    mkCase "err/n-neg" #[.slice valueA, .slice key4, .cell dict4Single, intV (-1)], -- [B3]
    mkCase "err/n-too-large" #[.slice valueA, .slice key4, .cell dict4Single, intV 1024], -- [B3]
    mkCase "err/n-nan" #[.slice valueA, .slice key4, .cell dict4Single, .int .nan], -- [B3]
    mkCase "err/type-dict" #[.slice valueA, .slice key4, .tuple #[], intV 4], -- [B4]
    mkCase "err/type-key" #[.slice valueA, .int (.num 0), .cell dict4Single, intV 4], -- [B4]
    mkCase "err/type-value" #[.int (.num 0), .slice key4, .cell dict4Single, intV 4], -- [B4]
    mkCase "err/key-short" #[.slice valueA, .slice key3, .cell dict4Single, intV 4], -- [B5]
    mkCase "err/key-short-n1" #[.slice valueA, .slice key3, .cell dict4Single, intV 1], -- [B5]
    mkCase "err/malformed-dict" #[.slice valueA, .slice key4, .cell malformedDict, intV 4], -- [B8]
    mkCase "err/malformed-dict-2" #[.slice valueA, .slice key4b, .cell malformedDict, intV 4], -- [B8]
    mkCaseCode "decode/raw/f41a" #[.slice valueA, .slice key4, .null, intV 4] rawOpcode, -- [B10][B11]
    mkCaseCode "decode/raw/f41b" #[.slice valueA, .slice key4, .null, intV 4] rawOpcodeRef, -- [B10][B11]
    mkCaseCode "decode/raw/f41c" #[.slice valueA, .slice key4, .null, intV 4] rawOpcodeInt, -- [B10][B11]
    mkCaseCode "decode/raw/f41d" #[.slice valueA, .slice key4, .null, intV 4] rawOpcodeIntRef, -- [B10][B11]
    mkCaseCode "decode/raw/f41e" #[.slice valueA, .slice key4, .null, intV 4] rawOpcodeUnsigned, -- [B10][B11]
    mkCaseCode "decode/raw/f41f" #[.slice valueA, .slice key4, .null, intV 4] rawOpcodeUnsignedRef, -- [B10][B11]
    mkCaseCode "decode/truncated8" #[] rawTruncated8, -- [B11]
    mkCaseCode "decode/gap" #[] rawOpcodeGap, -- [B11]
    mkCase "gas/exact/base-hit" #[.slice valueA, .slice key4c, .cell dict4Pair, intV 4] (mkGasProgram baseGas) gasBaseExact, -- [B11]
    mkCase "gas/exact/base-minus-one-hit" #[.slice valueA, .slice key4c, .cell dict4Pair, intV 4] (mkGasProgram baseGasMinusOne) gasBaseExactMinusOne, -- [B11]
    mkCase "gas/exact/insert" #[.slice valueA, .slice key4d, .null, intV 4] (mkGasProgram insertGas) gasInsertExact, -- [B11]
    mkCase "gas/exact/insert-minus-one" #[.slice valueA, .slice key4d, .null, intV 4] (mkGasProgram insertGasMinusOne) gasInsertExactMinusOne, -- [B11]
    mkCase "gas/exact/base0" #[.slice valueA, .slice key0, .null, intV 0] (mkGasProgram baseGas) gasBaseExact, -- [B11]
    mkCase "gas/exact/insert0" #[.slice valueB, .slice key0, .null, intV 0] (mkGasProgram insertGas) gasInsertExact, -- [B11]
    mkCase "gas/exact-minus-one/insert0" #[.slice valueB, .slice key0, .null, intV 0] (mkGasProgram insertGasMinusOne) gasInsertExactMinusOne -- [B11]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTSETGETFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTSETGET
