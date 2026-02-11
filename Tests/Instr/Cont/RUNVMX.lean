import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.RUNVMX

private def runvmxId : InstrId := { name := "RUNVMX" }
private def runvmxInstr : Instr := .contExt .runvmx

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

private def dataOrdA : Cell := Cell.mkOrdinary (natToBits 0x2a 6) #[]
private def dataOrdB : Cell := Cell.mkOrdinary (natToBits 0x15 5) #[dataOrdA]
private def dataPrunedMask1 : Cell := mkPrunedMask1 9

private def childCodeRet : Cell :=
  assembleNoRefCell! "runvmx/child/ret" #[.ret]

private def childCodePush7Ret : Cell :=
  assembleNoRefCell! "runvmx/child/push7-ret" #[.pushInt (.num 7), .ret]

private def childCodePush23Ret : Cell :=
  assembleNoRefCell! "runvmx/child/push2-push3-ret"
    #[.pushInt (.num 2), .pushInt (.num 3), .ret]

private def childCodeAdd : Cell :=
  assembleNoRefCell! "runvmx/child/add" #[.add]

private def childCodeInvalid15 : Cell :=
  Cell.mkOrdinary (natToBits 0xdb50 15) #[]

private def childCodeImplicitJmpRef : Cell :=
  Cell.mkOrdinary #[] #[childCodePush7Ret]

private def modeNeedsRetVals (mode : Nat) : Bool := (mode &&& 256) = 256
private def modeNeedsData (mode : Nat) : Bool := (mode &&& 4) = 4
private def modeNeedsC7 (mode : Nat) : Bool := (mode &&& 16) = 16
private def modeNeedsGasLimit (mode : Nat) : Bool := (mode &&& 8) = 8
private def modeNeedsGasMax (mode : Nat) : Bool := (mode &&& 64) = 64

private def mkRunvmxInitRaw
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
    st.push (intV (Int.ofNat mode))

private def mkRunvmxInit
    (mode : Nat)
    (childItems : Array Value)
    (codeCell : Cell)
    (retVals : Nat := 0)
    (dataCell : Cell := dataOrdA)
    (c7 : Array Value := #[])
    (gasLimit : Int := 1_000_000)
    (gasMax : Int := 2_000_000) : Array Value :=
  mkRunvmxInitRaw mode childItems childItems.size codeCell retVals dataCell c7 gasLimit gasMax

private def mkRunvmxOracleCase
    (name : String)
    (initStack : Array Value)
    (program : Array Instr := #[runvmxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := runvmxId
    program := program
    initStack := initStack
    gasLimits := gasLimits
    fuel := fuel }

private def intStackAsc (n : Nat) : Array Value :=
  Array.ofFn (n := n) fun i => intV (Int.ofNat (i.1 + 1))

private def mixedChildStack : Array Value :=
  #[.null, intV (-3), .cell dataOrdB, .slice (Slice.ofCell dataOrdA), .builder Builder.empty, .tuple #[], .cont (.quit 0)]

private def gasOverInfty : Int := GasLimits.infty + 1
private def retValsOverMax : Int := Int.ofNat ((1 <<< 30) + 1)

private def runRunvmxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect (execInstrFlowRunvm nativeHost) runvmxInstr stack

private def oracleCases : Array OracleCase :=
  #[
    -- Mode-bit coverage on successful children.
    mkRunvmxOracleCase "ok/mode0/empty-ret"
      (mkRunvmxInit 0 #[] childCodeRet),
    mkRunvmxOracleCase "ok/mode0/one-int-ret"
      (mkRunvmxInit 0 #[intV 5] childCodeRet),
    mkRunvmxOracleCase "ok/mode0/two-int-ret"
      (mkRunvmxInit 0 #[intV 1, intV 2] childCodeRet),
    mkRunvmxOracleCase "ok/mode0/push7ret-empty"
      (mkRunvmxInit 0 #[] childCodePush7Ret),
    mkRunvmxOracleCase "ok/mode0/push23ret-with-arg"
      (mkRunvmxInit 0 #[intV 9] childCodePush23Ret),
    mkRunvmxOracleCase "ok/mode1/samec3-no-push0"
      (mkRunvmxInit 1 #[] childCodeRet),
    mkRunvmxOracleCase "ok/mode2/push0-ignored-without-samec3"
      (mkRunvmxInit 2 #[] childCodeRet),
    mkRunvmxOracleCase "ok/mode3/push0-active"
      (mkRunvmxInit 3 #[] childCodeRet),
    mkRunvmxOracleCase "ok/mode4/with-data"
      (mkRunvmxInit 4 #[] childCodeRet (dataCell := dataOrdB)),
    mkRunvmxOracleCase "ok/mode8/return-gas"
      (mkRunvmxInit 8 #[intV 11] childCodePush7Ret (gasLimit := 500_000)),
    mkRunvmxOracleCase "ok/mode16/load-c7-empty-tuple"
      (mkRunvmxInit 16 #[] childCodeRet (c7 := #[])),
    mkRunvmxOracleCase "ok/mode24/load-c7-plus-return-gas"
      (mkRunvmxInit 24 #[intV 3] childCodeRet (c7 := #[]) (gasLimit := 600_000)),
    mkRunvmxOracleCase "ok/mode32/return-actions"
      (mkRunvmxInit 32 #[] childCodeRet),
    mkRunvmxOracleCase "ok/mode36/return-data-and-actions"
      (mkRunvmxInit 36 #[] childCodeRet (dataCell := dataOrdB)),
    mkRunvmxOracleCase "ok/mode64/hardmax-only"
      (mkRunvmxInit 64 #[] childCodeRet (gasMax := 750_000)),
    mkRunvmxOracleCase "ok/mode72/hardmax-and-gas-limit"
      (mkRunvmxInit 72 #[] childCodeRet (gasLimit := 250_000) (gasMax := 150_000)),
    mkRunvmxOracleCase "ok/mode128/isolated-gas"
      (mkRunvmxInit 128 #[intV 1, intV 2] childCodeRet),
    mkRunvmxOracleCase "ok/mode256/retvals-0"
      (mkRunvmxInit 256 #[] childCodePush7Ret (retVals := 0)),
    mkRunvmxOracleCase "ok/mode256/retvals-1"
      (mkRunvmxInit 256 #[] childCodePush7Ret (retVals := 1)),
    mkRunvmxOracleCase "ok/mode257/samec3-and-retvals-1"
      (mkRunvmxInit 257 #[] childCodePush7Ret (retVals := 1)),
    mkRunvmxOracleCase "ok/mode511/all-flags-minimal"
      (mkRunvmxInit 511 #[] childCodeRet (retVals := 0) (dataCell := dataOrdB) (c7 := #[]) (gasLimit := 500_000) (gasMax := 700_000)),

    -- Child execution shape coverage.
    mkRunvmxOracleCase "ok/child/implicit-jmpref"
      (mkRunvmxInit 0 #[] childCodeImplicitJmpRef),
    mkRunvmxOracleCase "ok/stack/preserve-below-not-copied"
      (mkRunvmxInitRaw 0 #[intV 999, intV 41, intV 42] 2 childCodeRet),
    mkRunvmxOracleCase "ok/stack/deep-mixed-values"
      (mkRunvmxInit 0 mixedChildStack childCodeRet),
    mkRunvmxOracleCase "ok/stack/copy-eight-ints"
      (mkRunvmxInit 0 (intStackAsc 8) childCodeRet),

    -- Top-level mode / setup errors.
    mkRunvmxOracleCase "err/mode/negative"
      #[intV (-1)],
    mkRunvmxOracleCase "err/mode/too-large-512"
      #[intV 512],
    mkRunvmxOracleCase "err/mode/too-large-4095"
      #[intV 4095],
    mkRunvmxOracleCase "err/mode/nan-program"
      #[]
      #[.pushInt .nan, runvmxInstr],
    mkRunvmxOracleCase "err/underflow/missing-code-and-stacksize"
      #[intV 0],
    mkRunvmxOracleCase "err/type/code-not-slice"
      #[intV 0, .null, intV 0],
    mkRunvmxOracleCase "err/range/stacksize-negative"
      #[intV (-1), .slice (Slice.ofCell childCodeRet), intV 0],
    mkRunvmxOracleCase "err/range/stacksize-too-large"
      #[intV 2, .slice (Slice.ofCell childCodeRet), intV 0],
    mkRunvmxOracleCase "err/full-flags/missing-optional-tail"
      #[intV 511],

    -- Optional-argument type/range failures.
    mkRunvmxOracleCase "err/type/with-data-not-cell"
      #[intV 0, .slice (Slice.ofCell childCodeRet), .null, intV 4],
    mkRunvmxOracleCase "err/type/load-c7-not-tuple"
      #[intV 0, .slice (Slice.ofCell childCodeRet), intV 7, intV 16],
    mkRunvmxOracleCase "err/range/gas-limit-negative"
      #[intV 0, .slice (Slice.ofCell childCodeRet), intV (-1), intV 8],
    mkRunvmxOracleCase "err/range/gas-limit-over-infty"
      #[intV 0, .slice (Slice.ofCell childCodeRet), intV gasOverInfty, intV 8],
    mkRunvmxOracleCase "err/range/gas-max-negative"
      #[intV 0, .slice (Slice.ofCell childCodeRet), intV 1000, intV (-1), intV 72],
    mkRunvmxOracleCase "err/range/retvals-negative"
      #[intV 0, .slice (Slice.ofCell childCodeRet), intV (-1), intV 256],
    mkRunvmxOracleCase "err/range/retvals-too-large"
      #[intV 0, .slice (Slice.ofCell childCodeRet), intV retValsOverMax, intV 256],

    -- Child-failure and restoration paths.
    mkRunvmxOracleCase "err/child/add-underflow"
      (mkRunvmxInit 0 #[] childCodeAdd),
    mkRunvmxOracleCase "err/retvals/not-enough-results"
      (mkRunvmxInit 256 #[] childCodePush7Ret (retVals := 2)),
    mkRunvmxOracleCase "err/commit/level-nonzero-c4"
      (mkRunvmxInit 4 #[] childCodeRet (dataCell := dataPrunedMask1)),
    mkRunvmxOracleCase "err/commit/level-nonzero-c4-and-c5"
      (mkRunvmxInit 36 #[] childCodeRet (dataCell := dataPrunedMask1))
  ]

def suite : InstrSuite where
  id := runvmxId
  unit := #[
    { name := "unit/raw/rangechk-on-nan-mode"
      run := do
        expectErr "nan/mode" (runRunvmxDirect #[.int .nan]) .rangeChk }
    ,
    { name := "unit/raw/rangechk-on-nan-gas-limit"
      run := do
        expectErr "nan/gas-limit"
          (runRunvmxDirect #[intV 0, .slice (Slice.ofCell childCodeRet), .int .nan, intV 8])
          .rangeChk }
    ,
    { name := "unit/raw/rangechk-on-nan-gas-max"
      run := do
        expectErr "nan/gas-max"
          (runRunvmxDirect #[intV 0, .slice (Slice.ofCell childCodeRet), intV 1000, .int .nan, intV 72])
          .rangeChk }
    ,
    { name := "unit/raw/rangechk-on-nan-stack-size"
      run := do
        expectErr "nan/stack-size"
          (runRunvmxDirect #[.int .nan, .slice (Slice.ofCell childCodeRet), intV 0])
          .rangeChk }
    ,
    { name := "unit/raw/commit-rejects-nonzero-level-c4"
      run := do
        let st := mkRunvmxInit 4 #[] childCodeRet (dataCell := dataPrunedMask1)
        expectOkStack "commit/nonzero-level"
          (runRunvmxDirect st)
          #[intV 0, intV Excno.cellOv.toInt, .null] }
  ]
  oracle := oracleCases
  fuzz := #[ mkReplayOracleFuzzSpec runvmxId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.RUNVMX
