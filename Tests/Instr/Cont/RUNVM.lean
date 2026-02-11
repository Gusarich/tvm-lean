import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.RUNVM

private def runvmId : InstrId := { name := "RUNVM" }

private def runvmInstr (mode : Nat) : Instr := .contExt (.runvm mode)

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def bytesToBits (bs : Array UInt8) : BitString :=
  bs.foldl (fun acc b => acc ++ natToBits b.toNat 8) #[]

private def depthToBytes2 (d : Nat) : Array UInt8 :=
  #[UInt8.ofNat ((d >>> 8) &&& 0xff), UInt8.ofNat (d &&& 0xff)]

private def mkPrunedMask1 (d0 : Nat) : Cell :=
  let bytes : Array UInt8 :=
    #[UInt8.ofNat 1, UInt8.ofNat 1]
      ++ Array.replicate 32 (UInt8.ofNat 0)
      ++ depthToBytes2 d0
  { bits := bytesToBits bytes, refs := #[], special := true, levelMask := 1 }

private def runvmWord24 (mode : Nat) : Nat :=
  (0xdb4 <<< 12) + (mode &&& 0xfff)

private def runvmRawOpcodeCell (mode : Nat) (tailBits : BitString := #[]) : Cell :=
  Cell.mkOrdinary (natToBits (runvmWord24 mode) 24 ++ tailBits) #[]

private def runvmTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def runvmTruncated12Code : Cell :=
  Cell.mkOrdinary (natToBits 0xdb4 12) #[]

private def runvmTruncated23Code : Cell :=
  Cell.mkOrdinary (natToBits (runvmWord24 341 >>> 1) 23) #[]

private def runvmRawWithTailCode : Cell :=
  runvmRawOpcodeCell 3 (natToBits 0xaa 8)

private def dataOrdA : Cell := Cell.mkOrdinary (natToBits 0x2a 6) #[]
private def dataOrdB : Cell := Cell.mkOrdinary (natToBits 0x15 5) #[dataOrdA]
private def dataPrunedMask1 : Cell := mkPrunedMask1 9

private def childCodeRet : Cell :=
  assembleNoRefCell! "runvm/child/ret" #[.ret]

private def childCodePush7Ret : Cell :=
  assembleNoRefCell! "runvm/child/push7-ret" #[.pushInt (.num 7), .ret]

private def childCodePush23Ret : Cell :=
  assembleNoRefCell! "runvm/child/push2-push3-ret"
    #[.pushInt (.num 2), .pushInt (.num 3), .ret]

private def childCodeAdd : Cell :=
  assembleNoRefCell! "runvm/child/add" #[.add]

private def childCodeInvalid15 : Cell :=
  Cell.mkOrdinary (natToBits 0xdb50 15) #[]

private def childCodeImplicitJmpRef : Cell :=
  Cell.mkOrdinary #[] #[childCodePush7Ret]

private def modeNeedsRetVals (mode : Nat) : Bool := (mode &&& 256) = 256
private def modeNeedsData (mode : Nat) : Bool := (mode &&& 4) = 4
private def modeNeedsC7 (mode : Nat) : Bool := (mode &&& 16) = 16
private def modeNeedsGasLimit (mode : Nat) : Bool := (mode &&& 8) = 8
private def modeNeedsGasMax (mode : Nat) : Bool := (mode &&& 64) = 64

private def mkRunvmInitRaw
    (mode : Nat)
    (allItems : Array Value)
    (stackSize : Nat)
    (codeCell : Cell)
    (retVals : Nat := 0)
    (dataCell : Cell := dataOrdA)
    (c7 : Array Value := #[])
    (gasLimit : Int := 1_000_000)
    (gasMax : Int := 2_000_000) : Array Value :=
  Id.run do
    let mut st : Array Value :=
      allItems ++ #[intV (Int.ofNat stackSize), .slice (Slice.ofCell codeCell)]
    if modeNeedsRetVals mode then
      st := st.push (intV (Int.ofNat retVals))
    if modeNeedsData mode then
      st := st.push (.cell dataCell)
    if modeNeedsC7 mode then
      st := st.push (.tuple c7)
    if modeNeedsGasLimit mode then
      st := st.push (intV gasLimit)
    if modeNeedsGasMax mode then
      st := st.push (intV gasMax)
    st

private def mkRunvmInit
    (mode : Nat)
    (childItems : Array Value)
    (codeCell : Cell)
    (retVals : Nat := 0)
    (dataCell : Cell := dataOrdA)
    (c7 : Array Value := #[])
    (gasLimit : Int := 1_000_000)
    (gasMax : Int := 2_000_000) : Array Value :=
  mkRunvmInitRaw mode childItems childItems.size codeCell retVals dataCell c7 gasLimit gasMax

private def mkRunvmOracleCase
    (name : String)
    (initStack : Array Value)
    (program : Array Instr := #[runvmInstr 0])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := runvmId
    program := program
    initStack := initStack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRunvmCodeCase
    (name : String)
    (initStack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := runvmId
    codeCell? := some code
    initStack := initStack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRunvmRawOpcodeCase
    (name : String)
    (mode : Nat)
    (initStack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkRunvmCodeCase name initStack (runvmRawOpcodeCell mode) gasLimits fuel

private def intStackAsc (n : Nat) : Array Value :=
  Array.ofFn (n := n) fun i => intV (Int.ofNat (i.1 + 1))

private def mixedChildStack : Array Value :=
  #[.null, intV (-3), .cell dataOrdB, .slice (Slice.ofCell dataOrdA), .builder Builder.empty, .tuple #[],
    .cont (.quit 0)]

private def gasOverInfty : Int := GasLimits.infty + 1
private def retValsOverMax : Int := Int.ofNat ((1 <<< 30) + 1)

private def runRunvmDirect (mode : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect (execInstrFlowRunvm nativeHost) (runvmInstr mode) stack

private def runRunvmRaw
    (mode : Nat)
    (stack : Array Value)
    (chksgnCounter : Nat := 0)
    (loadedCells : Array (Array UInt8) := #[])
    (libraries : Array Cell := #[]) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      chksgnCounter := chksgnCounter
      loadedCells := loadedCells
      libraries := libraries }
  (execInstrFlowRunvm nativeHost (runvmInstr mode) (pure ())).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error, got {reprStr instr}/{bits}")

private def expectDecodeRunvm
    (label : String)
    (code : Cell)
    (expectedMode : Nat)
    (expectedTailBits : Nat := 0) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .contExt (.runvm expectedMode) then
        throw (IO.userError s!"{label}: expected .contExt (.runvm {expectedMode}), got {reprStr instr}")
      else if bits != 24 then
        throw (IO.userError s!"{label}: expected decoded bits 24, got {bits}")
      else if rest.bitsRemaining != expectedTailBits then
        throw (IO.userError s!"{label}: expected tail bits {expectedTailBits}, got {rest.bitsRemaining}")
      else if rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected zero refs in decode tail, got {rest.refsRemaining}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def oracleCases : Array OracleCase :=
  #[
    -- Core mode-bit coverage on successful children.
    mkRunvmOracleCase "ok/mode0/empty-ret"
      (mkRunvmInit 0 #[] childCodeRet)
      #[runvmInstr 0],
    mkRunvmOracleCase "ok/mode0/one-int-ret"
      (mkRunvmInit 0 #[intV 5] childCodeRet)
      #[runvmInstr 0],
    mkRunvmOracleCase "ok/mode0/two-int-ret"
      (mkRunvmInit 0 #[intV 1, intV 2] childCodeRet)
      #[runvmInstr 0],
    mkRunvmOracleCase "ok/mode0/push7ret-empty"
      (mkRunvmInit 0 #[] childCodePush7Ret)
      #[runvmInstr 0],
    mkRunvmOracleCase "ok/mode0/push23ret-with-arg"
      (mkRunvmInit 0 #[intV 9] childCodePush23Ret)
      #[runvmInstr 0],
    mkRunvmOracleCase "ok/mode1/samec3-no-push0"
      (mkRunvmInit 1 #[] childCodeRet)
      #[runvmInstr 1],
    mkRunvmOracleCase "ok/mode2/push0-ignored-without-samec3"
      (mkRunvmInit 2 #[] childCodeRet)
      #[runvmInstr 2],
    mkRunvmOracleCase "ok/mode3/push0-active"
      (mkRunvmInit 3 #[] childCodeRet)
      #[runvmInstr 3],
    mkRunvmOracleCase "ok/mode4/with-data"
      (mkRunvmInit 4 #[] childCodeRet (dataCell := dataOrdB))
      #[runvmInstr 4],
    mkRunvmOracleCase "ok/mode8/return-gas"
      (mkRunvmInit 8 #[intV 11] childCodePush7Ret (gasLimit := 500_000))
      #[runvmInstr 8],
    mkRunvmOracleCase "ok/mode16/load-c7-empty-tuple"
      (mkRunvmInit 16 #[] childCodeRet (c7 := #[]))
      #[runvmInstr 16],
    mkRunvmOracleCase "ok/mode24/load-c7-plus-return-gas"
      (mkRunvmInit 24 #[intV 3] childCodeRet (c7 := #[]) (gasLimit := 600_000))
      #[runvmInstr 24],
    mkRunvmOracleCase "ok/mode32/return-actions"
      (mkRunvmInit 32 #[] childCodeRet)
      #[runvmInstr 32],
    mkRunvmOracleCase "ok/mode36/return-data-and-actions"
      (mkRunvmInit 36 #[] childCodeRet (dataCell := dataOrdB))
      #[runvmInstr 36],
    mkRunvmOracleCase "ok/mode64/hardmax-only"
      (mkRunvmInit 64 #[] childCodeRet (gasMax := 750_000))
      #[runvmInstr 64],
    mkRunvmOracleCase "ok/mode72/hardmax-and-gas-limit"
      (mkRunvmInit 72 #[] childCodeRet (gasLimit := 250_000) (gasMax := 150_000))
      #[runvmInstr 72],
    mkRunvmOracleCase "ok/mode128/isolated-gas"
      (mkRunvmInit 128 #[intV 1, intV 2] childCodeRet)
      #[runvmInstr 128],
    mkRunvmOracleCase "ok/mode256/retvals-0"
      (mkRunvmInit 256 #[] childCodePush7Ret (retVals := 0))
      #[runvmInstr 256],
    mkRunvmOracleCase "ok/mode256/retvals-1"
      (mkRunvmInit 256 #[] childCodePush7Ret (retVals := 1))
      #[runvmInstr 256],
    mkRunvmOracleCase "ok/mode257/samec3-and-retvals-1"
      (mkRunvmInit 257 #[] childCodePush7Ret (retVals := 1))
      #[runvmInstr 257],
    mkRunvmOracleCase "ok/mode511/all-flags-minimal"
      (mkRunvmInit 511 #[] childCodeRet (retVals := 0) (dataCell := dataOrdB) (c7 := #[])
        (gasLimit := 500_000) (gasMax := 700_000))
      #[runvmInstr 511],

    -- Child execution shape and decode-failure behavior.
    mkRunvmOracleCase "ok/child/implicit-jmpref"
      (mkRunvmInit 0 #[] childCodeImplicitJmpRef)
      #[runvmInstr 0],
    mkRunvmOracleCase "ok/stack/preserve-below-not-copied"
      (mkRunvmInitRaw 0 #[intV 999, intV 41, intV 42] 2 childCodeRet)
      #[runvmInstr 0],
    mkRunvmOracleCase "ok/stack/deep-mixed-values"
      (mkRunvmInit 0 mixedChildStack childCodeRet)
      #[runvmInstr 0],
    mkRunvmOracleCase "ok/stack/copy-eight-ints"
      (mkRunvmInit 0 (intStackAsc 8) childCodeRet)
      #[runvmInstr 0],
    mkRunvmOracleCase "err/child/add-underflow"
      (mkRunvmInit 0 #[] childCodeAdd)
      #[runvmInstr 0],
    mkRunvmOracleCase "err/child/decode-invalid-15bit"
      (mkRunvmInit 0 #[] childCodeInvalid15)
      #[runvmInstr 0],

    -- Setup/type/range failures.
    mkRunvmOracleCase "err/underflow/missing-code-and-stacksize"
      #[]
      #[runvmInstr 0],
    mkRunvmOracleCase "err/type/code-not-slice"
      #[intV 0, .null]
      #[runvmInstr 0],
    mkRunvmOracleCase "err/range/stacksize-negative"
      #[intV (-1), .slice (Slice.ofCell childCodeRet)]
      #[runvmInstr 0],
    mkRunvmOracleCase "err/range/stacksize-too-large"
      #[intV 2, .slice (Slice.ofCell childCodeRet)]
      #[runvmInstr 0],
    mkRunvmOracleCase "err/full-flags/missing-optional-tail"
      #[]
      #[runvmInstr 511],
    mkRunvmOracleCase "err/type/with-data-not-cell"
      #[intV 0, .slice (Slice.ofCell childCodeRet), .null]
      #[runvmInstr 4],
    mkRunvmOracleCase "err/type/load-c7-not-tuple"
      #[intV 0, .slice (Slice.ofCell childCodeRet), intV 7]
      #[runvmInstr 16],
    mkRunvmOracleCase "err/range/gas-limit-negative"
      #[intV 0, .slice (Slice.ofCell childCodeRet), intV (-1)]
      #[runvmInstr 8],
    mkRunvmOracleCase "err/range/gas-limit-over-infty"
      #[intV 0, .slice (Slice.ofCell childCodeRet), intV gasOverInfty]
      #[runvmInstr 8],
    mkRunvmOracleCase "err/range/gas-max-negative"
      #[intV 0, .slice (Slice.ofCell childCodeRet), intV 1000, intV (-1)]
      #[runvmInstr 72],
    mkRunvmOracleCase "err/range/retvals-negative"
      #[intV 0, .slice (Slice.ofCell childCodeRet), intV (-1)]
      #[runvmInstr 256],
    mkRunvmOracleCase "err/range/retvals-too-large"
      #[intV 0, .slice (Slice.ofCell childCodeRet), intV retValsOverMax]
      #[runvmInstr 256],
    mkRunvmOracleCase "err/retvals/not-enough-results"
      (mkRunvmInit 256 #[] childCodePush7Ret (retVals := 2))
      #[runvmInstr 256],
    mkRunvmOracleCase "err/commit/level-nonzero-c4"
      (mkRunvmInit 4 #[] childCodeRet (dataCell := dataPrunedMask1))
      #[runvmInstr 4],
    mkRunvmOracleCase "err/commit/level-nonzero-c4-and-c5"
      (mkRunvmInit 36 #[] childCodeRet (dataCell := dataPrunedMask1))
      #[runvmInstr 36],

    -- Immediate-mode raw-opcode coverage (24-bit prefix and invalid immediate values).
    mkRunvmRawOpcodeCase "ok/raw-opcode/mode0/basic"
      0
      (mkRunvmInit 0 #[] childCodeRet),
    mkRunvmRawOpcodeCase "ok/raw-opcode/mode3/push0-active"
      3
      (mkRunvmInit 3 #[] childCodeRet),
    mkRunvmRawOpcodeCase "ok/raw-opcode/mode511/full-flags"
      511
      (mkRunvmInit 511 #[] childCodeRet (retVals := 0) (dataCell := dataOrdB) (c7 := #[])
        (gasLimit := 500_000) (gasMax := 700_000)),
    mkRunvmRawOpcodeCase "err/raw-opcode/mode512-rangechk"
      512
      #[],
    mkRunvmRawOpcodeCase "err/raw-opcode/mode4095-rangechk"
      4095
      #[intV 0, .slice (Slice.ofCell childCodeRet)],

    -- Immediate decode boundaries from raw code cells.
    mkRunvmCodeCase "err/raw-opcode/truncated-8-prefix"
      #[]
      runvmTruncated8Code,
    mkRunvmCodeCase "err/raw-opcode/truncated-12-prefix"
      #[intV 5]
      runvmTruncated12Code,
    mkRunvmCodeCase "err/raw-opcode/truncated-23-prefix"
      #[.null, intV 6]
      runvmTruncated23Code
  ]

def suite : InstrSuite where
  id := runvmId
  unit := #[
    { name := "unit/raw/immediate-helper-masks-to-12-bits"
      run := do
        let init := mkRunvmInit 0 #[] childCodeRet
        match runRunvmDirect 0 init, runRunvmDirect 4096 init with
        | .ok base, .ok masked =>
            if masked != base then
              throw (IO.userError s!"mask-helper: expected same stack as mode0, got {reprStr masked} vs {reprStr base}")
            else
              pure ()
        | .error e, _ =>
            throw (IO.userError s!"mask-helper/base: expected success, got {e}")
        | _, .error e =>
            throw (IO.userError s!"mask-helper/masked: expected success, got {e}") }
    ,
    { name := "unit/raw/rangechk-on-nan-gas-limit"
      run := do
        expectErr "nan/gas-limit"
          (runRunvmDirect 8 #[intV 0, .slice (Slice.ofCell childCodeRet), .int .nan])
          .rangeChk }
    ,
    { name := "unit/raw/rangechk-on-nan-gas-max"
      run := do
        expectErr "nan/gas-max"
          (runRunvmDirect 72 #[intV 0, .slice (Slice.ofCell childCodeRet), intV 1000, .int .nan])
          .rangeChk }
    ,
    { name := "unit/raw/rangechk-on-nan-stack-size"
      run := do
        expectErr "nan/stack-size"
          (runRunvmDirect 0 #[.int .nan, .slice (Slice.ofCell childCodeRet)])
          .rangeChk }
    ,
    { name := "unit/decode/raw-immediate-24bit"
      run := do
        expectDecodeRunvm "decode/raw-mode0" (runvmRawOpcodeCell 0) 0
        expectDecodeRunvm "decode/raw-mode257" (runvmRawOpcodeCell 257) 257
        expectDecodeRunvm "decode/raw-with-tail" runvmRawWithTailCode 3 8 }
    ,
    { name := "unit/decode/raw-immediate-truncated-prefixes"
      run := do
        expectDecodeErr "decode/truncated-8" runvmTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-12" runvmTruncated12Code .invOpcode
        expectDecodeErr "decode/truncated-23" runvmTruncated23Code .invOpcode }
    ,
    { name := "unit/regression/non-isolated-propagates-loaded-cells"
      run := do
        let st ←
          expectRawOk "loaded/non-isolated"
            (runRunvmRaw 0 (mkRunvmInit 0 #[] childCodeImplicitJmpRef))
        if st.loadedCells.size != 1 then
          throw (IO.userError
            s!"loaded/non-isolated: expected loadedCells.size=1, got {st.loadedCells.size}")
        else
          pure () }
    ,
    { name := "unit/regression/isolated-does-not-propagate-loaded-cells"
      run := do
        let st ←
          expectRawOk "loaded/isolated"
            (runRunvmRaw 128 (mkRunvmInit 128 #[] childCodeImplicitJmpRef))
        if st.loadedCells.size != 0 then
          throw (IO.userError
            s!"loaded/isolated: expected loadedCells.size=0, got {st.loadedCells.size}")
        else
          pure () }
    ,
    { name := "unit/regression/isolated-resets-chksgn-counter"
      run := do
        let st ←
          expectRawOk "chksgn/isolated-reset"
            (runRunvmRaw 128 (mkRunvmInit 128 #[] childCodeRet) (chksgnCounter := 7))
        if st.chksgnCounter != 0 then
          throw (IO.userError s!"chksgn/isolated-reset: expected 0, got {st.chksgnCounter}")
        else
          pure () }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkReplayOracleFuzzSpec runvmId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.RUNVM
