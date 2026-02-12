import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.JMPREF

/-
JMPREF branch map (Lean vs C++ `exec_do_with_ref` + `st->jump`):
- Decode/ref guard:
  - cp0 `0xdb3d` + one reference decodes to `.jmpRef`;
  - missing/truncated ref payload fails with `invOpcode` (`takeRefInv` / `have_refs(1)`).
- Ref-to-cont conversion:
  - ordinary referenced cells convert to ordinary continuations;
  - special/exotic referenced cells fail with `cellUnd` after load registration,
    matching `ref_to_cont(load_cell_slice_ref(...))`.
- Jump path:
  - execution is unconditional after successful conversion;
  - taken path uses `VM.jump`, i.e. the same entrypoint as C++ `VmState::jump`
    (including corrected shared jump-adjust semantics for continuations that carry cdata).
-/

private def jmprefId : InstrId := { name := "JMPREF" }

private def jmprefOpcode : Nat := 0xdb3d

private def jmprefInstr (code : Slice) : Instr :=
  .jmpRef code

private def dispatchSentinel : Int := 90137
private def jumpMarker : Int := 333
private def tailMarker : Int := 777

private def q0 : Value := .cont (.quit 0)

private def noiseCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[]

private def noiseCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[noiseCellA]

private def fullSliceNoise : Slice :=
  Slice.ofCell noiseCellB

private def specialTargetCell : Cell :=
  { bits := natToBits 2 8 ++ Array.replicate 256 false
    refs := #[]
    special := true
    levelMask := 0 }

private def opcodeBits : BitString :=
  natToBits jmprefOpcode 16

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.size = 0 then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def assembleNoRefBits! (label : String) (program : Array Instr) : BitString :=
  (assembleNoRefCell! label program).bits

private def mkJmprefCode (target : Cell) (tail : Array Instr := #[]) : Cell :=
  Cell.mkOrdinary (opcodeBits ++ assembleNoRefBits! "jmpref/tail" tail) #[target]

private def targetMarkerCell : Cell :=
  assembleNoRefCell! "jmpref/target-marker" #[.pushInt (.num jumpMarker)]

private def targetAddCell : Cell :=
  assembleNoRefCell! "jmpref/target-add" #[.add]

private def branchObservableCode : Cell :=
  mkJmprefCode targetMarkerCell #[.pushInt (.num tailMarker)]

private def noTailCode : Cell :=
  mkJmprefCode targetMarkerCell #[]

private def addObservableCode : Cell :=
  mkJmprefCode targetAddCell #[.pushInt (.num tailMarker)]

private def specialBranchCode : Cell :=
  mkJmprefCode specialTargetCell #[.pushInt (.num tailMarker)]

private def missingRefCode : Cell :=
  Cell.mkOrdinary opcodeBits #[]

private def missingRefWithTailCode : Cell :=
  Cell.mkOrdinary
    (opcodeBits ++ assembleNoRefBits! "jmpref/missing-ref-tail" #[.pushInt (.num tailMarker)])
    #[]

private def truncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def truncated15Code : Cell :=
  Cell.mkOrdinary ((natToBits jmprefOpcode 16).take 15) #[]

private def emptyCode : Cell :=
  Cell.empty

private def runJmprefDirect
    (code : Slice)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowJmpRef (jmprefInstr code) stack

private def runJmprefDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowJmpRef instr (VM.push (intV dispatchSentinel)) stack

private def runJmprefRaw
    (code : Slice)
    (stack : Array Value)
    (cc : Continuation := .quit 71)
    (loaded : Array (Array UInt8) := #[])
    (gas : GasLimits := GasLimits.default) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      loadedCells := loaded
      gas := gas }
  (execInstrFlowJmpRef (jmprefInstr code) (pure ())).run st0

private def runJmprefState
    (code : Slice)
    (stack : Array Value)
    (cc : Continuation := .quit 71)
    (loaded : Array (Array UInt8) := #[])
    (gas : GasLimits := GasLimits.default) : Except Excno VmState :=
  let (res, st1) := runJmprefRaw code stack cc loaded gas
  match res with
  | .ok _ => .ok st1
  | .error e => .error e

private def sameSlice (a b : Slice) : Bool :=
  a.bitPos == b.bitPos && a.refPos == b.refPos && a.cell == b.cell

private def regsEq (x y : Regs) : Bool :=
  x.c0 == y.c0 && x.c1 == y.c1 && x.c2 == y.c2 && x.c3 == y.c3 &&
  x.c4 == y.c4 && x.c5 == y.c5 && x.c7 == y.c7

private def expectStateJumpedToCode
    (label : String)
    (res : Except Excno VmState)
    (expectedCode : Slice)
    (expectedStack : Array Value)
    (expectedLoaded : Nat) : IO Unit := do
  match res with
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")
  | .ok st =>
      if st.stack != expectedStack then
        throw (IO.userError s!"{label}: expected stack {reprStr expectedStack}, got {reprStr st.stack}")
      else if st.loadedCells.size != expectedLoaded then
        throw (IO.userError s!"{label}: expected loadedCells={expectedLoaded}, got {st.loadedCells.size}")
      else
        match st.cc with
        | .ordinary code _ _ _ =>
            if sameSlice code expectedCode then
              pure ()
            else
              throw (IO.userError s!"{label}: expected jump code {reprStr expectedCode}, got {reprStr code}")
        | _ =>
            throw (IO.userError s!"{label}: expected ordinary continuation, got {reprStr st.cc}")

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
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def expectDecodeOkJmpref
    (label : String)
    (code : Cell)
    (expectedTarget : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (.jmpRef s, bits, rest) =>
      if bits != 16 then
        throw (IO.userError s!"{label}: expected decoded bits=16, got {bits}")
      else if rest.refPos != 1 then
        throw (IO.userError s!"{label}: expected decoded refPos=1, got {rest.refPos}")
      else if !(sameSlice s (Slice.ofCell expectedTarget)) then
        throw (IO.userError s!"{label}: decoded target mismatch")
      else
        pure ()
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected JMPREF, got instr={reprStr instr}, bits={bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (code : Cell := branchObservableCode)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := jmprefId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def jmprefOracleFamilies : Array String :=
  #[
    "jump/observable/",
    "jump/no-tail/",
    "jump/target-add/",
    "special/cellund/",
    "decode/missing-ref/",
    "decode/missing-ref-with-tail/",
    "decode/truncated-",
    "decode/empty-code"
  ]

private def jmprefFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := jmprefOracleFamilies
    mutationModes := #[
      0, 0, 0, 0,
      1, 1, 1,
      2, 2,
      3, 3, 3,
      4
    ]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def jmprefNoisePool : Array (Array Value) :=
  #[#[], #[intV 1], #[.null], #[.cell noiseCellA], #[.slice fullSliceNoise], #[.builder Builder.empty], #[q0]]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genJmprefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (noise, rng2) := pickFromPool jmprefNoisePool rng1
  let case0 :=
    if shape = 0 then
      mkCase "fuzz/ok/jump-observable" noise branchObservableCode
    else if shape = 1 then
      mkCase "fuzz/ok/no-tail" noise noTailCode
    else if shape = 2 then
      mkCase "fuzz/ok/target-add" (noise ++ #[intV 2, intV 3]) addObservableCode
    else if shape = 3 then
      mkCase "fuzz/err/special" noise specialBranchCode
    else if shape = 4 then
      mkCase "fuzz/err/decode/missing-ref" noise missingRefCode
    else if shape = 5 then
      mkCase "fuzz/err/decode/missing-ref-with-tail" noise missingRefWithTailCode
    else if shape = 6 then
      mkCase "fuzz/err/decode/truncated8" noise truncated8Code
    else if shape = 7 then
      mkCase "fuzz/err/decode/truncated15" noise truncated15Code
    else
      mkCase "fuzz/err/decode/empty-code" noise emptyCode
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := jmprefId
  unit := #[
    { name := "unit/direct/unconditional-jump-preserves-stack"
      run := do
        let targetSlice := Slice.ofCell targetMarkerCell
        let deep : Array Value := #[
          .null,
          intV 9,
          .cell noiseCellB,
          .slice fullSliceNoise,
          .builder Builder.empty,
          .tuple #[],
          q0,
          intV maxInt257,
          intV (minInt257 + 1)
        ]
        expectOkStack "direct/empty" (runJmprefDirect targetSlice #[]) #[]
        expectOkStack "direct/deep" (runJmprefDirect targetSlice deep) deep }
    ,
    { name := "unit/raw/cc-transition-load-effects-and-no-reg-mutation"
      run := do
        let base : VmState := VmState.initial Cell.empty
        let regsCustom : Regs :=
          { base.regs with
            c0 := .quit 10
            c1 := .quit 11
            c2 := .quit 12
            c3 := .quit 13 }
        let ccInit : Continuation := .quit 91
        let targetSlice := Slice.ofCell targetMarkerCell
        let stack0 : Array Value := #[.null, intV 5]

        let st0 : VmState :=
          { base with stack := stack0, cc := ccInit, regs := regsCustom }
        let (res, st1) := (execInstrFlowJmpRef (jmprefInstr targetSlice) (pure ())).run st0
        match res with
        | .error e =>
            throw (IO.userError s!"raw/jump: expected success, got {e}")
        | .ok _ =>
            if st1.stack != stack0 then
              throw (IO.userError s!"raw/jump: stack mismatch {reprStr st1.stack}")
            else if st1.loadedCells.size != 1 then
              throw (IO.userError s!"raw/jump: expected one loaded cell, got {st1.loadedCells.size}")
            else
              match st1.cc with
              | .ordinary code _ _ cdata =>
                  if !(sameSlice code targetSlice) then
                    throw (IO.userError s!"raw/jump: code mismatch {reprStr code}")
                  else if !(cdata.stack.isEmpty && cdata.nargs = -1) then
                    throw (IO.userError s!"raw/jump: cdata mismatch {reprStr cdata}")
                  else if !(regsEq st1.regs regsCustom) then
                    throw (IO.userError s!"raw/jump: regs changed {reprStr st1.regs}")
                  else
                    pure ()
              | _ =>
                  throw (IO.userError s!"raw/jump: expected ordinary cc, got {reprStr st1.cc}")

        let preloaded : Array (Array UInt8) := #[Cell.hashBytes targetMarkerCell]
        let (resLoaded, stLoaded) := runJmprefRaw targetSlice #[intV 1] (.quit 88) preloaded
        match resLoaded with
        | .error e =>
            throw (IO.userError s!"raw/reload: expected success, got {e}")
        | .ok _ =>
            if stLoaded.loadedCells != preloaded then
              throw (IO.userError s!"raw/reload: expected loaded cells unchanged, got {reprStr stLoaded.loadedCells}")
            else
              pure () }
    ,
    { name := "unit/special-cell-rejection-and-gas-ordering"
      run := do
        let specialSlice := Slice.ofCell specialTargetCell
        let targetSlice := Slice.ofCell targetMarkerCell
        let ccInit : Continuation := .quit 71

        let (resSpecial, stSpecial) := runJmprefRaw specialSlice #[intV 7] ccInit
        match resSpecial with
        | .error .cellUnd =>
            if stSpecial.stack != #[intV 7] then
              throw (IO.userError s!"special/cellund: stack mismatch {reprStr stSpecial.stack}")
            else if stSpecial.cc != ccInit then
              throw (IO.userError s!"special/cellund: cc changed {reprStr stSpecial.cc}")
            else if stSpecial.loadedCells.size != 1 then
              throw (IO.userError s!"special/cellund: expected one loaded cell, got {stSpecial.loadedCells.size}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"special/cellund: expected cellUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "special/cellund: expected cellUnd, got success")

        let tight : GasLimits := GasLimits.ofLimit 99
        let (resOogOrd, stOogOrd) := runJmprefRaw targetSlice #[intV 8] ccInit #[] tight
        match resOogOrd with
        | .error .outOfGas =>
            if stOogOrd.stack != #[intV 8] then
              throw (IO.userError s!"gas/ordinary-oom: stack mismatch {reprStr stOogOrd.stack}")
            else if stOogOrd.cc != ccInit then
              throw (IO.userError s!"gas/ordinary-oom: cc changed {reprStr stOogOrd.cc}")
            else if stOogOrd.loadedCells.size != 1 then
              throw (IO.userError s!"gas/ordinary-oom: expected one loaded cell, got {stOogOrd.loadedCells.size}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"gas/ordinary-oom: expected outOfGas, got {e}")
        | .ok _ =>
            throw (IO.userError "gas/ordinary-oom: expected outOfGas, got success")

        let (resOogSpecial, stOogSpecial) := runJmprefRaw specialSlice #[intV 9] ccInit #[] tight
        match resOogSpecial with
        | .error .outOfGas =>
            if stOogSpecial.stack != #[intV 9] then
              throw (IO.userError s!"gas/special-oom: stack mismatch {reprStr stOogSpecial.stack}")
            else if stOogSpecial.cc != ccInit then
              throw (IO.userError s!"gas/special-oom: cc changed {reprStr stOogSpecial.cc}")
            else if stOogSpecial.loadedCells.size != 1 then
              throw (IO.userError s!"gas/special-oom: expected one loaded cell, got {stOogSpecial.loadedCells.size}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"gas/special-oom: expected outOfGas, got {e}")
        | .ok _ =>
            throw (IO.userError "gas/special-oom: expected outOfGas, got success") }
    ,
    { name := "unit/decode-ref-guard-and-truncation"
      run := do
        expectDecodeOkJmpref "decode/ok" (mkJmprefCode targetMarkerCell #[]) targetMarkerCell
        expectDecodeErr "decode/missing-ref" missingRefCode .invOpcode
        expectDecodeErr "decode/missing-ref-with-tail" missingRefWithTailCode .invOpcode
        expectDecodeErr "decode/truncated-8bit" truncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15bit" truncated15Code .invOpcode
        expectDecodeErr "decode/empty" emptyCode .invOpcode }
    ,
    { name := "unit/dispatch-non-jmpref-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runJmprefDispatchFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectStateJumpedToCode "dispatch/match-jmpref"
          (runJmprefState (Slice.ofCell targetMarkerCell) #[intV 1] (.quit 55))
          (Slice.ofCell targetMarkerCell)
          #[intV 1]
          1 }
  ]
  oracle := #[
    mkCase "jump/observable/empty" #[] branchObservableCode,
    mkCase "jump/observable/int-zero" #[intV 0] branchObservableCode,
    mkCase "jump/observable/int-neg" #[intV (-5)] branchObservableCode,
    mkCase "jump/observable/deep-null-int" #[.null, intV 9] branchObservableCode,
    mkCase "jump/observable/deep-cell" #[.cell noiseCellB, intV 3] branchObservableCode,
    mkCase "jump/observable/deep-slice" #[.slice fullSliceNoise, intV 4] branchObservableCode,
    mkCase "jump/observable/deep-builder-tuple" #[.builder Builder.empty, .tuple #[], intV 6] branchObservableCode,
    mkCase "jump/observable/deep-maxint" #[intV maxInt257] branchObservableCode,
    mkCase "jump/observable/deep-minplus1" #[intV (minInt257 + 1)] branchObservableCode,
    mkCase "jump/observable/deep-cont" #[q0, intV 11] branchObservableCode,
    mkCase "jump/observable/deep-mixed-1" #[.null, .cell noiseCellA, .slice fullSliceNoise, intV 2] branchObservableCode,
    mkCase "jump/observable/deep-mixed-2" #[.builder Builder.empty, q0, intV (pow2 200)] branchObservableCode,
    mkCase "jump/observable/big-pos" #[intV (pow2 255)] branchObservableCode,
    mkCase "jump/observable/big-neg" #[intV (-(pow2 255))] branchObservableCode,

    mkCase "jump/no-tail/empty" #[] noTailCode,
    mkCase "jump/no-tail/int" #[intV 1] noTailCode,
    mkCase "jump/no-tail/deep-null" #[.null, intV 2] noTailCode,
    mkCase "jump/no-tail/deep-cell-slice" #[.cell noiseCellA, .slice fullSliceNoise, intV 3] noTailCode,
    mkCase "jump/no-tail/deep-builder" #[.builder Builder.empty, intV 4] noTailCode,
    mkCase "jump/no-tail/deep-cont" #[q0, intV 5] noTailCode,
    mkCase "jump/no-tail/deep-max" #[intV maxInt257, intV 6] noTailCode,

    mkCase "jump/target-add/basic-2-plus-3" #[intV 2, intV 3] addObservableCode,
    mkCase "jump/target-add/basic-10-plus-neg4" #[intV 10, intV (-4)] addObservableCode,
    mkCase "jump/target-add/zeros" #[intV 0, intV 0] addObservableCode,
    mkCase "jump/target-add/deep" #[.null, intV 7, intV 8] addObservableCode,

    mkCase "special/cellund/empty" #[] specialBranchCode,
    mkCase "special/cellund/int" #[intV 0] specialBranchCode,
    mkCase "special/cellund/deep-null" #[.null, intV 1] specialBranchCode,
    mkCase "special/cellund/deep-cell" #[.cell noiseCellB, intV 2] specialBranchCode,
    mkCase "special/cellund/deep-slice-builder" #[.slice fullSliceNoise, .builder Builder.empty, intV 3] specialBranchCode,
    mkCase "special/cellund/deep-cont" #[q0, intV 4] specialBranchCode,

    -- Oracle runner currently executes with default gas/c7 and does not apply
    -- `OracleGasLimits`; keep tight-gas expectations in unit/raw tests instead.

    mkCase "decode/missing-ref/empty" #[] missingRefCode,
    mkCase "decode/missing-ref/int" #[intV 0] missingRefCode,
    mkCase "decode/missing-ref/deep" #[.null, intV 1] missingRefCode,
    mkCase "decode/missing-ref/type-noise" #[.cell noiseCellA] missingRefCode,
    mkCase "decode/missing-ref-with-tail/empty" #[] missingRefWithTailCode,
    mkCase "decode/missing-ref-with-tail/deep" #[.tuple #[], intV 2] missingRefWithTailCode,
    mkCase "decode/truncated-8bit-prefix" #[intV 0] truncated8Code,
    mkCase "decode/truncated-15bit-prefix" #[intV 0] truncated15Code,
    mkCase "decode/empty-code" #[intV 0] emptyCode
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr jmprefId
      count := 500
      gen := genJmprefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.JMPREF
