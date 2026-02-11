import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.ENDC

/-
ENDC branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Endc.lean` (`.endc`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc9` decode)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.endc` encode to `0xc9`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_builder_to_cell`, opcode `0xc9`).

Branch map used for this suite:
- dispatch guard (`.endc` vs fallback `next`);
- top-of-stack pop via `VM.popBuilder`: `stkUnd` / `typeChk` / success;
- success path finalizes builder to ordinary cell and charges `cellCreateGasPrice`.
-/

private def endcId : InstrId := { name := "ENDC" }

private def endcInstr : Instr := .endc

private def endcOpcode : Nat := 0xc9

private def dispatchSentinel : Int := 509

private def mkEndcCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[endcInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := endcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkEndcProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := endcId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runEndcDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellEndc endcInstr stack

private def runEndcDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellEndc instr (VM.push (intV dispatchSentinel)) stack

private def runEndcRaw (stack : Array Value) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrCellEndc endcInstr (pure ())).run st0
  (res, st1)

private def gasForInstrWithFallback (instr : Instr) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok budget => budget
  | .error _ => instrGas instr 16

private def endcSetGasNeed (n : Int) : Int :=
  gasForInstrWithFallback (.pushInt (.num n))
    + gasForInstrWithFallback (.tonEnvOp .setGasLimit)
    + gasForInstrWithFallback endcInstr
    + cellCreateGasPrice
    + implicitRetGasPrice

private def endcExactGasBudgetFixedPoint (n : Int) : Nat → Int
  | 0 => n
  | k + 1 =>
      let n' := endcSetGasNeed n
      if n' = n then n else endcExactGasBudgetFixedPoint n' k

private def endcSetGasExact : Int :=
  endcExactGasBudgetFixedPoint 64 20

private def endcSetGasExactMinusOne : Int :=
  if endcSetGasExact > 0 then endcSetGasExact - 1 else 0

private def refLeafB : Cell := Cell.mkOrdinary (natToBits 22 5) #[refLeafA]

private def refLeafC : Cell := Cell.mkOrdinary (stripeBits 11 1) #[refLeafA, Cell.empty]

private def refSpecial : Cell :=
  { bits := natToBits 2 8 ++ Array.replicate 256 false
    refs := #[]
    special := true
    levelMask := 3 }

private def refPool : Array Cell :=
  #[refLeafA, refLeafB, refLeafC, refSpecial]

private def pickRefs (refs : Nat) : Array Cell :=
  Array.ofFn (n := refs) fun i => refPool[i.1 % refPool.size]!

private def mkBuilderWithBitsRefs (bits refs : Nat) (phase : Nat := 0) : Builder :=
  { bits := stripeBits bits phase
    refs := pickRefs refs }

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt x, .xchg0 1, .stu bits]

private def mkBuilderProgram
    (bits refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkEndcProgram
    (bits refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bits refs x ++ #[endcInstr]

private def mkEndcProgramWithNoise
    (bits refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.pushNull] ++ mkEndcProgram bits refs x

private def mkEndcProgram1023 (refs : Nat) : Array Instr :=
  build1023WithFixed .stu ++ appendRefsToTopBuilder refs ++ #[endcInstr]

private def endcBitsPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 63, 127, 255, 256]

private def pickEndcBits (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (endcBitsPool.size - 1)
  (endcBitsPool[idx]!, rng')

private def pickEndcRefs (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 4

private def maxUnsignedByBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 bits - 1

private def pickUnsignedForBits (bits : Nat) (rng0 : StdGen) : IntVal × StdGen :=
  if bits = 0 then
    (.num 0, rng0)
  else
    let hi := maxUnsignedByBits bits
    let (pick, rng1) := randNat rng0 0 4
    let x : Int :=
      if pick = 0 then 0
      else if pick = 1 then 1
      else if pick = 2 then hi
      else if pick = 3 then
        if hi > 0 then hi - 1 else 0
      else
        hi / 2
    (.num x, rng1)

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 73
    else .cell Cell.empty
  (v, rng1)

private def genEndcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  if shape = 0 then
    (mkEndcCase "fuzz/ok/direct/empty-builder" #[.builder Builder.empty], rng1)
  else if shape = 1 then
    let (noise, rng2) := pickNoiseValue rng1
    (mkEndcCase "fuzz/ok/direct/deep-stack"
      #[noise, .builder Builder.empty], rng2)
  else if shape = 2 then
    (mkEndcCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 3 then
    (mkEndcCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 4 then
    (mkEndcCase "fuzz/type/top-int" #[intV 0], rng1)
  else if shape = 5 then
    (mkEndcCase "fuzz/type/top-cell" #[.cell Cell.empty], rng1)
  else if shape = 6 then
    (mkEndcCase "fuzz/type/top-slice" #[.slice (Slice.ofCell Cell.empty)], rng1)
  else if shape = 7 then
    let (bits, rng2) := pickEndcBits rng1
    let (x, rng3) := pickUnsignedForBits bits rng2
    (mkEndcProgramCase s!"fuzz/ok/program/bits-{bits}" #[]
      (mkEndcProgram bits 0 x), rng3)
  else if shape = 8 then
    let (refs, rng2) := pickEndcRefs rng1
    (mkEndcProgramCase s!"fuzz/ok/program/refs-{refs}" #[]
      (mkEndcProgram 0 refs), rng2)
  else if shape = 9 then
    let (bits, rng2) := pickEndcBits rng1
    let (refs, rng3) := pickEndcRefs rng2
    let (x, rng4) := pickUnsignedForBits bits rng3
    (mkEndcProgramCase s!"fuzz/ok/program/bits-{bits}-refs-{refs}-noise" #[]
      (mkEndcProgramWithNoise bits refs x), rng4)
  else if shape = 10 then
    (mkEndcCase "fuzz/gas/exact" #[.builder Builder.empty]
      #[.pushInt (.num endcSetGasExact), .tonEnvOp .setGasLimit, endcInstr], rng1)
  else if shape = 11 then
    (mkEndcCase "fuzz/gas/exact-minus-one" #[.builder Builder.empty]
      #[.pushInt (.num endcSetGasExactMinusOne), .tonEnvOp .setGasLimit, endcInstr], rng1)
  else
    let (refs, rng2) := pickEndcRefs rng1
    (mkEndcProgramCase s!"fuzz/ok/program/1023bits-refs-{refs}" #[]
      (mkEndcProgram1023 refs), rng2)

def suite : InstrSuite where
  id := endcId
  unit := #[
    { name := "unit/direct/success-finalize-across-builder-shapes"
      run := do
        let b0 : Builder := Builder.empty
        let b1 : Builder := mkBuilderWithBitsRefs 1 0
        let b2 : Builder := mkBuilderWithBitsRefs 7 2 1
        let b3 : Builder := mkBuilderWithBitsRefs 255 4
        let b4 : Builder := { bits := stripeBits 9 0, refs := #[refSpecial, refLeafB] }
        let checks : Array Builder := #[b0, b1, b2, b3, b4]
        for b in checks do
          expectOkStack s!"ok/bits-{b.bits.size}-refs-{b.refs.size}"
            (runEndcDirect #[.builder b]) #[.cell b.finalize] }
    ,
    { name := "unit/direct/success-boundary-1023bits-4refs"
      run := do
        let boundary : Builder := mkBuilderWithBitsRefs 1023 4 1
        expectOkStack "ok/boundary/1023bits-4refs"
          (runEndcDirect #[.builder boundary])
          #[.cell boundary.finalize] }
    ,
    { name := "unit/direct/preserves-below-stack"
      run := do
        let bA : Builder := mkBuilderWithBitsRefs 0 0
        let bB : Builder := mkBuilderWithBitsRefs 8 3
        let below : Array Value := #[.null, intV 19, .cell refLeafA]
        expectOkStack "ok/preserve-below/empty"
          (runEndcDirect (below ++ #[.builder bA]))
          (below ++ #[.cell bA.finalize])
        expectOkStack "ok/preserve-below/nonempty"
          (runEndcDirect (below ++ #[.builder bB]))
          (below ++ #[.cell bB.finalize]) }
    ,
    { name := "unit/direct/underflow-and-type-errors"
      run := do
        expectErr "underflow/empty" (runEndcDirect #[]) .stkUnd

        let bads : Array (String × Value) :=
          #[
            ("null", .null),
            ("int", intV 0),
            ("cell", .cell Cell.empty),
            ("slice", .slice (Slice.ofCell Cell.empty)),
            ("tuple", .tuple #[]),
            ("continuation", .cont (.quit 0))
          ]
        for (label, v) in bads do
          expectErr s!"type/{label}" (runEndcDirect #[v]) .typeChk }
    ,
    { name := "unit/direct/error-order-top-first"
      run := do
        expectErr "type/top-null-over-valid-builder"
          (runEndcDirect #[.builder Builder.empty, .null]) .typeChk
        expectOkStack "ok/top-builder-below-null-preserved"
          (runEndcDirect #[.null, .builder Builder.empty]) #[.null, .cell Cell.empty] }
    ,
    { name := "unit/direct/gas-charge-success-vs-errors"
      run := do
        let b : Builder := mkBuilderWithBitsRefs 11 2
        let (okRes, okState) := runEndcRaw #[.builder b]
        match okRes with
        | .error e =>
            throw (IO.userError s!"expected success, got {e}")
        | .ok _ =>
            if okState.stack != #[.cell b.finalize] then
              throw (IO.userError
                s!"unexpected success stack: {reprStr okState.stack}")
            if okState.gas.gasConsumed != cellCreateGasPrice then
              throw (IO.userError
                s!"expected gasConsumed={cellCreateGasPrice}, got {okState.gas.gasConsumed}")

        let (typeRes, typeState) := runEndcRaw #[.null]
        match typeRes with
        | .ok _ => throw (IO.userError "expected typeChk error")
        | .error e =>
            if e != .typeChk then
              throw (IO.userError s!"expected typeChk, got {e}")
        if typeState.gas.gasConsumed != 0 then
          throw (IO.userError
            s!"type error should not consume gas, got {typeState.gas.gasConsumed}")

        let (undRes, undState) := runEndcRaw #[]
        match undRes with
        | .ok _ => throw (IO.userError "expected stkUnd error")
        | .error e =>
            if e != .stkUnd then
              throw (IO.userError s!"expected stkUnd, got {e}")
        if undState.gas.gasConsumed != 0 then
          throw (IO.userError
            s!"underflow should not consume gas, got {undState.gas.gasConsumed}") }
    ,
    { name := "unit/opcode/decode-and-assemble-boundaries"
      run := do
        let assembled ←
          match assembleCp0 [endcInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/endc failed: {e}")
        if assembled.bits = natToBits endcOpcode 8 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/endc expected 0xc9 bits, got {reprStr assembled.bits}")

        let s0 := Slice.ofCell assembled
        let s1 ← expectDecodeStep "decode/assembled-endc" s0 endcInstr 8
        if s1.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/assembled-endc expected exhausted slice, got {s1.bitsRemaining} bits")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xc8 8 ++
          natToBits endcOpcode 8 ++
          natToBits 0xca 8 ++ natToBits 0x00 8 ++
          natToBits 0xcd 8 ++
          natToBits 0xcc 8 ++
          addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-newc" r0 .newc 8
        let r2 ← expectDecodeStep "decode/raw-endc" r1 endcInstr 8
        let r3 ← expectDecodeStep "decode/raw-sti1" r2 (.sti 1) 16
        let r4 ← expectDecodeStep "decode/raw-endcst" r3 .endcst 8
        let r5 ← expectDecodeStep "decode/raw-stref" r4 .stref 8
        let r6 ← expectDecodeStep "decode/raw-tail-add" r5 .add 8
        if r6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw expected exhausted slice, got {r6.bitsRemaining}")

        let payload := natToBits 0x5a 8
        let rawWord := mkSliceFromBits (natToBits endcOpcode 8 ++ payload)
        let rest ← expectDecodeStep "decode/raw-word" rawWord endcInstr 8
        if rest.readBits 8 = payload then
          pure ()
        else
          throw (IO.userError "decode/raw-word did not preserve trailing payload bits")

        match decodeCp0WithBits (mkSliceFromBits (natToBits endcOpcode 7)) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/truncated expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "decode/truncated expected invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-endc-falls-through"
      run := do
        let b : Builder := mkBuilderWithBitsRefs 6 1
        expectOkStack "dispatch/add"
          (runEndcDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/newc"
          (runEndcDispatchFallback .newc #[.builder b])
          #[.builder b, intV dispatchSentinel]
        expectOkStack "dispatch/stref"
          (runEndcDispatchFallback .stref #[intV 7])
          #[intV 7, intV dispatchSentinel] }
  ]
  oracle := #[
    mkEndcCase "ok/init/empty-builder"
      #[.builder Builder.empty],
    mkEndcCase "ok/init/empty-builder-deep-stack"
      #[.null, intV 11, .builder Builder.empty],

    mkEndcCase "underflow/empty" #[],
    mkEndcCase "type/top-null" #[.null],
    mkEndcCase "type/top-int" #[intV 0],
    mkEndcCase "type/top-cell" #[.cell Cell.empty],
    mkEndcCase "type/top-slice" #[.slice (Slice.ofCell Cell.empty)],
    mkEndcCase "type/top-tuple-empty" #[.tuple #[]],
    mkEndcCase "type/top-cont-quit0" #[.cont (.quit 0)],
    mkEndcCase "type/top-null-over-builder" #[.builder Builder.empty, .null],

    mkEndcProgramCase "ok/program/newc-endc-empty"
      #[] (mkEndcProgram 0 0),
    mkEndcProgramCase "ok/program/bits1"
      #[] (mkEndcProgram 1 0 (.num 1)),
    mkEndcProgramCase "ok/program/bits8"
      #[] (mkEndcProgram 8 0 (.num 173)),
    mkEndcProgramCase "ok/program/bits15"
      #[] (mkEndcProgram 15 0 (.num 10923)),
    mkEndcProgramCase "ok/program/bits255"
      #[] (mkEndcProgram 255 0 (.num 0)),
    mkEndcProgramCase "ok/program/bits256"
      #[] (mkEndcProgram 256 0 (.num 0)),
    mkEndcProgramCase "ok/program/bits1023-refs0"
      #[] (mkEndcProgram1023 0),
    mkEndcProgramCase "ok/program/refs1"
      #[] (mkEndcProgram 0 1),
    mkEndcProgramCase "ok/program/refs4"
      #[] (mkEndcProgram 0 4),
    mkEndcProgramCase "ok/program/bits7-refs3-noise"
      #[] (mkEndcProgramWithNoise 7 3 (.num 85)),

    mkEndcCase "gas/exact-succeeds"
      #[.builder Builder.empty]
      #[.pushInt (.num endcSetGasExact), .tonEnvOp .setGasLimit, endcInstr],
    mkEndcCase "gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty]
      #[.pushInt (.num endcSetGasExactMinusOne), .tonEnvOp .setGasLimit, endcInstr]
  ]
  fuzz := #[
    { seed := 2026021001
      count := 500
      gen := genEndcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.ENDC
