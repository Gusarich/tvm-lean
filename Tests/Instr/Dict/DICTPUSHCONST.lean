import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTPUSHCONST

/-!
INSTRUCTION: DICTPUSHCONST

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime dispatch.
   - `execInstrDictDictPushConst` handles only `.dictPushConst`.
   - Non-matching instructions must fall through via `next`.

2. [B2] Runtime semantics for `.dictPushConst`.
   - Pushes the embedded dictionary cell as `.cell` and then pushes `Int.ofNat keyBits`.
   - No runtime stack popping, no type checking, no range/overflow checks in this handler.

3. [B3] Stack-shape preservation.
   - All existing stack elements must remain below the two newly pushed values.

4. [B4] Assembler behavior.
   - `assembleCp0` rejects `.dictPushConst` with `.invOpcode` for all arguments.

5. [B5] Decoder match range.
   - `decodeCp0WithBits` matches `0xf4a400 <= w24 < 0xf4a800`.
   - Matching opcodes decode as `.dictPushConst dictCell n` with 24-bit progress.

6. [B6] Decoder payload extraction.
   - Decoded `n` comes from the low 10 bits of the 24-bit opcode.
   - Decoding consumes and stores the inline reference as the pushed dictionary cell.

7. [B7] Boundary opcodes.
   - Lower boundary is `0xf4a400` (`n=0`).
   - Upper boundary is `0xf4a7ff` (`n=1023`).

8. [B8] Decoder invalid ref guard.
   - Valid opcode families without an attached reference return `.invOpcode` (`takeRefInv` path).

9. [B9] Decoder bit-length guard.
   - `haveBits 24` must pass before `haveRefs`.
   - Truncated opcodes return `.invOpcode`.

10. [B10] Adjacent invalid opcodes.
    - `0xf4a3ff` and `0xf4a800` must decode as `.invOpcode`.

11. [B11] Gas accounting.
    - No variable gas penalty in Lean/C++ path; fixed base cost only.
    - Validate exact budget success and exact-minus-one failure behavior.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is expected to be covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTPUSHCONST" }

private def dispatchSentinel : Int := 98765

private def rawOpcodeBase : Nat := 0xf4a400

private def makeRaw24 (n : Nat) : Nat :=
  rawOpcodeBase + (n &&& 0x3ff)

private def makeRawCode (n : Nat) (ref : Cell) (tail : BitString := #[]) : Cell :=
  Cell.mkOrdinary (natToBits (makeRaw24 n) 24 ++ tail) #[ref]

private def makeRawCodeNoRef (n : Nat) (tail : BitString := #[]) : Cell :=
  Cell.mkOrdinary (natToBits (makeRaw24 n) 24 ++ tail) #[]

private def rawLowerInvalid : Nat := 0xf4a3ff

private def rawUpperInvalid : Nat := 0xf4a800

private def dictCellA : Cell := Cell.mkOrdinary (natToBits 0xA1A1 16) #[]
private def dictCellB : Cell := Cell.mkOrdinary (natToBits 0xB2B2 16) #[]
private def dictCellC : Cell := Cell.mkOrdinary (natToBits 0xC3C3 16) #[]
private def dictCellD : Cell := Cell.mkOrdinary (natToBits 0xD4D4 16) #[]
private def dictCellNoise : Cell := Cell.mkOrdinary (natToBits 0xDEAD 16) #[]

private def rawInvalidLower : Cell := Cell.mkOrdinary (natToBits rawLowerInvalid 24) #[]
private def rawInvalidUpper : Cell := Cell.mkOrdinary (natToBits rawUpperInvalid 24) #[]

private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits (makeRaw24 77) 8) #[]
private def rawTruncated23 : Cell := Cell.mkOrdinary (natToBits (makeRaw24 78) 23) #[dictCellA]
private def rawMissingRef8bit : Cell := makeRawCodeNoRef 79
private def rawMissingRefTail : Cell := makeRawCodeNoRef 80 (natToBits 0xf40a 16)

private def dictPushGas : Int := computeExactGasBudget (.dictPushConst dictCellA 0)
private def dictPushGasMinusOne : Int := computeExactGasBudgetMinusOne (.dictPushConst dictCellA 0)

private def dictPushGasLimitsExact : OracleGasLimits := oracleGasLimitsExact dictPushGas
private def dictPushGasLimitsExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne dictPushGasMinusOne

private def runDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictPushConst instr (VM.push (intV dispatchSentinel)) stack

private def mkExpectedStack
    (root : Cell)
    (keyBits : Nat)
    (stack : Array Value) : Array Value :=
  stack ++ #[.cell root, intV (Int.ofNat keyBits)]

private def mkCase
    (name : String)
    (root : Cell)
    (keyBits : Nat)
    (stack : Array Value := #[])
    (program : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let p : Array Instr := if program.isEmpty then #[.dictPushConst root keyBits] else program
  { name := name
    instr := suiteId
    program := p
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
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

private def expectAssembleInvOpcode (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok c =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr c}")
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def expectDecodeInvOpcode (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode => pure ()
  | .ok (i, bits, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {reprStr i} with {bits} bits")
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")

private def pickRoot (i : Nat) : Cell :=
  match i with
  | 0 => dictCellA
  | 1 => dictCellB
  | 2 => dictCellC
  | _ => dictCellD

private def pickStack (i : Nat) : Array Value :=
  match i with
  | 0 => #[]
  | 1 => #[intV 1, .cell dictCellNoise]
  | 2 => #[.null, intV (-1)]
  | 3 => #[.tuple #[], .builder Builder.empty]
  | _ => #[.slice (Slice.ofCell dictCellNoise), .null, intV 7]

private def pickN (i : Nat) : Nat :=
  match i with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 42
  | 4 => 255
  | 5 => 1023
  | 6 => 1024
  | 7 => 4096
  | _ => 1_000_000

private def genDictPushConstFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (rootIdx, rng2) := randNat rng1 0 3
  let (tailIdx, rng3) := randNat rng2 0 4
  let (nIdx, rng4) := randNat rng3 0 7
  let root := pickRoot rootIdx
  let stack := pickStack tailIdx
  let n := pickN nIdx
  let case0 :=
    if shape = 0 then
      mkCase "fuzz/ok/0" root 0 stack
    else if shape = 1 then
      mkCase "fuzz/ok/1" root 1 stack
    else if shape = 2 then
      mkCase "fuzz/ok/2" root 2 stack
    else if shape = 3 then
      mkCase "fuzz/ok/42" root 42 stack
    else if shape = 4 then
      mkCase "fuzz/ok/255" root 255 stack
    else if shape = 5 then
      mkCase "fuzz/ok/1023" root 1023 stack
    else if shape = 6 then
      mkCase "fuzz/ok/1024" root 1024 stack
    else if shape = 7 then
      mkCase "fuzz/ok/1000000" root 1000000 (if stack.isEmpty then #[] else stack)
    else if shape = 8 then
      mkCodeCase "fuzz/raw/ok/0" stack (makeRawCode 0 root (natToBits 0xf40a 16))
    else if shape = 9 then
      mkCodeCase "fuzz/raw/ok/1023" stack (makeRawCode 1023 root)
    else if shape = 10 then
      mkCodeCase "fuzz/raw/ok/mixed" stack (Cell.mkOrdinary (natToBits (makeRaw24 31) 24 ++ natToBits 0xf4a0 16) #[root])
    else if shape = 11 then
      mkCodeCase "fuzz/raw/ok/chain" stack (makeRawCode 7 root (natToBits 0xf40b 16))
    else if shape = 12 then
      mkCodeCase "fuzz/raw/err/missing-ref" stack rawMissingRef8bit
    else if shape = 13 then
      mkCodeCase "fuzz/raw/err/missing-ref-tail" stack rawMissingRefTail
    else if shape = 14 then
      mkCodeCase "fuzz/raw/err/truncated-23" stack rawTruncated23
    else if shape = 15 then
      mkCodeCase "fuzz/raw/err/truncated-8" stack rawTruncated8
    else if shape = 16 then
      mkCodeCase "fuzz/raw/err/invalid-lower" stack rawInvalidLower
    else if shape = 17 then
      mkCodeCase "fuzz/raw/err/invalid-upper" stack rawInvalidUpper
    else if shape = 18 then
      mkCase "fuzz/gas/exact" root n
        (program := #[.pushInt (.num dictPushGas), .tonEnvOp .setGasLimit, .dictPushConst root n])
        (gasLimits := dictPushGasLimitsExact)
    else if shape = 19 then
      mkCase "fuzz/gas/exact-minus-one" root n
        (program := #[.pushInt (.num dictPushGasMinusOne), .tonEnvOp .setGasLimit, .dictPushConst root n])
        (gasLimits := dictPushGasLimitsExactMinusOne)
    else if shape = 20 then
      mkCase "fuzz/ok/boundary-0" root 0 (program := #[.dictPushConst root 0])
    else
      mkCase "fuzz/ok/boundary-1023" root 1023 (program := #[.dictPushConst root 1023])
  let (tag, rng5) := randNat rng4 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng5)


def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let stack := #[intV 1, .cell dictCellA, intV 2]
        let matched := runDispatchFallback (.dictPushConst dictCellB 1) #[]
        expectOkStack "unit/dispatch/match" matched (#[.cell dictCellB, intV 1])
        let fallback := runDispatchFallback (.add) stack
        expectOkStack "unit/dispatch/non-match" fallback (stack ++ #[intV dispatchSentinel]) },
    { name := "unit/runtime/push-null-like-noise" -- [B2]
      run := do
        let init := #[intV 11, .builder Builder.empty, .slice (Slice.ofCell dictCellC)]
        let out := runHandlerDirect execInstrDictDictPushConst (.dictPushConst dictCellA 0) init
        expectOkStack "unit/runtime/push" out (mkExpectedStack dictCellA 0 init) },
    { name := "unit/runtime/preserve-tail-values" -- [B2][B3]
      run := do
        let init := #[.null, intV 7, .cell dictCellB, .tuple #[]]
        let out := runHandlerDirect execInstrDictDictPushConst (.dictPushConst dictCellD 1023) init
        expectOkStack "unit/runtime/preserve" out (mkExpectedStack dictCellD 1023 init) },
    { name := "unit/runtime/large-keybits-is-accepted" -- [B2]
      run := do
        let init := #[.cell dictCellNoise]
        let out := runHandlerDirect execInstrDictDictPushConst (.dictPushConst dictCellC 1_000_000) init
        expectOkStack "unit/runtime/large" out (mkExpectedStack dictCellC 1_000_000 init) },
    { name := "unit/asm/invOpcode" -- [B4]
      run := do
        expectAssembleInvOpcode "unit/asm/low" (.dictPushConst dictCellA 0)
        expectAssembleInvOpcode "unit/asm/mid" (.dictPushConst dictCellA 255)
        expectAssembleInvOpcode "unit/asm/high" (.dictPushConst dictCellA 1023) },
    { name := "unit/decode/chains" -- [B5][B6][B10]
      run := do
        let code0 : Cell := makeRawCode 0 dictCellA (natToBits 0xf40a 16)
        let s1 ← expectDecodeStep "unit/decode/chain-0" (Slice.ofCell code0) (.dictPushConst dictCellA 0) 24
        let _ ← expectDecodeStep "unit/decode/chain-next" s1 (.dictGet false false false) 16
        let code1023 : Cell := makeRawCode 1023 dictCellB (natToBits 0xf40b 16)
        let s2 ← expectDecodeStep "unit/decode/chain-1023" (Slice.ofCell code1023) (.dictPushConst dictCellB 1023) 24
        let _ ← expectDecodeStep "unit/decode/chain-1023-next" s2 (.dictGet false false true) 16 },
    { name := "unit/decode/errors" -- [B7][B8][B9]
      run := do
        expectDecodeInvOpcode "unit/decode/invalid-lower" rawInvalidLower
        expectDecodeInvOpcode "unit/decode/invalid-upper" rawInvalidUpper
        expectDecodeInvOpcode "unit/decode/missing-ref" rawMissingRef8bit
        expectDecodeInvOpcode "unit/decode/missing-ref-tail" rawMissingRefTail
        expectDecodeInvOpcode "unit/decode/truncated-23" rawTruncated23
        expectDecodeInvOpcode "unit/decode/truncated-8" rawTruncated8 }
  ]
  oracle := #[
    mkCase "oracle/ok/direct/null/0" dictCellA 0, -- [B2]
    mkCase "oracle/ok/direct/null/1" dictCellA 1, -- [B2]
    mkCase "oracle/ok/direct/null/2" dictCellA 2, -- [B2]
    mkCase "oracle/ok/direct/null/255" dictCellA 255, -- [B2]
    mkCase "oracle/ok/direct/null/1023" dictCellA 1023, -- [B2]
    mkCase "oracle/ok/direct/null/1024" dictCellA 1024, -- [B2]
    mkCase "oracle/ok/direct/null/4096" dictCellA 4096, -- [B2]
    mkCase "oracle/ok/direct/null/large" dictCellA 1_000_000, -- [B2]
    mkCase "oracle/ok/direct/null/tail-a" dictCellA 16 #[intV 1, .null], -- [B2][B3]
    mkCase "oracle/ok/direct/null/tail-b" dictCellA 17 #[.cell dictCellB, intV 7, .builder Builder.empty], -- [B2][B3]
    mkCase "oracle/ok/direct/cell-b/0" dictCellB 0, -- [B2]
    mkCase "oracle/ok/direct/cell-b/7" dictCellB 7, -- [B2]
    mkCase "oracle/ok/direct/cell-b/1023" dictCellB 1023, -- [B2]
    mkCase "oracle/ok/direct/cell-c/255" dictCellC 255, -- [B2]
    mkCase "oracle/ok/direct/cell-c/4096" dictCellC 4096, -- [B2]
    mkCase "oracle/ok/direct/cell-c/tail" dictCellC 777 #[.null, intV 123, .slice (Slice.ofCell dictCellA)], -- [B2][B3]
    mkCase "oracle/ok/direct/cell-d/0" dictCellD 0, -- [B2]
    mkCase "oracle/ok/direct/cell-d/1024" dictCellD 1024, -- [B2]
    mkCase "oracle/ok/direct/cell-d/tail" dictCellD 1234 #[.cell dictCellNoise, intV (-9), .tuple #[]], -- [B2][B3]
    mkCodeCase "oracle/raw/ok/0" #[] (makeRawCode 0 dictCellA), -- [B5][B6]
    mkCodeCase "oracle/raw/ok/1" #[] (makeRawCode 1 dictCellA), -- [B5][B6]
    mkCodeCase "oracle/raw/ok/42" #[] (makeRawCode 42 dictCellB), -- [B5][B6]
    mkCodeCase "oracle/raw/ok/255" #[] (makeRawCode 255 dictCellC), -- [B5][B6]
    mkCodeCase "oracle/raw/ok/1023" #[] (makeRawCode 1023 dictCellD), -- [B5][B6]
    mkCodeCase "oracle/raw/ok/chain/0" #[] (Cell.mkOrdinary (natToBits (makeRaw24 4) 24 ++ natToBits 0xf40a 16) #[dictCellA]), -- [B5][B6][B10]
    mkCodeCase "oracle/raw/ok/chain/1023" #[] (Cell.mkOrdinary (natToBits (makeRaw24 1023) 24 ++ natToBits 0xf40b 16) #[dictCellB]), -- [B5][B6][B10]
    mkCase "oracle/gas/exact" dictCellA 0
      (program := #[.pushInt (.num dictPushGas), .tonEnvOp .setGasLimit, .dictPushConst dictCellA 0])
      (gasLimits := dictPushGasLimitsExact), -- [B11]
    mkCase "oracle/gas/exact-minus-one" dictCellA 0
      (program := #[.pushInt (.num dictPushGasMinusOne), .tonEnvOp .setGasLimit, .dictPushConst dictCellA 0])
      (gasLimits := dictPushGasLimitsExactMinusOne), -- [B11]
    mkCodeCase "oracle/raw/err/missing-ref" #[] rawMissingRef8bit, -- [B8]
    mkCodeCase "oracle/raw/err/missing-ref-tail" #[] rawMissingRefTail, -- [B8]
    mkCodeCase "oracle/raw/err/truncated-23" #[] rawTruncated23, -- [B9]
    mkCodeCase "oracle/raw/err/truncated-8" #[] rawTruncated8, -- [B9]
    mkCodeCase "oracle/raw/err/invalid-lower" #[] rawInvalidLower, -- [B7]
    mkCodeCase "oracle/raw/err/invalid-upper" #[] rawInvalidUpper -- [B7]
  ]
  fuzz := #[
    {
      seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictPushConstFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTPUSHCONST
