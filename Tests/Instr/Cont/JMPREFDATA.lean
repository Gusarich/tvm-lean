import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.JMPREFDATA

/-
JMPREFDATA branch map (Lean vs C++ `contops.cpp`):
- decode path (`0xdb3e`):
  - require full 16-bit opcode and one embedded ref (`have_refs(1)` / `takeRefInv`);
  - missing/truncated opcode/ref => `invOpcode`.
- exec path (`exec_do_with_ref` + JMPREFDATA lambda):
  1) convert ref to continuation (`ref_to_cont(load_cell_slice_ref)`):
     load gas registration + special/exotic rejection (`cell_und`);
  2) `push_code()` pushes current remaining code slice;
  3) `jump(cont)` transfers control to the referenced continuation.
- ordering property:
  `push_code` must occur after successful ref conversion and before jump.
-/

private def jmprefdataId : InstrId := { name := "JMPREFDATA" }

private def jmprefdataOpcode : Nat := 0xdb3e

private def dispatchSentinel : Int := 91871

private def jmprefdataInstr (target : Cell) : Instr :=
  .jmpRefData (Slice.ofCell target)

private def bytesToBits (bytes : Array Nat) : BitString :=
  bytes.foldl (fun acc b => acc ++ natToBits (b % 256) 8) #[]

private def mkCodeCell (bytes : Array Nat) (refs : Array Cell := #[]) : Cell :=
  Cell.mkOrdinary (bytesToBits bytes) refs

private def mkJmprefdataCodeCell (target : Cell) (tailBytes : Array Nat := #[]) : Cell :=
  mkCodeCell (#[0xdb, 0x3e] ++ tailBytes) #[target]

private def mkJmprefdataCodeCellWithExtraRefs
    (target : Cell)
    (tailBytes : Array Nat := #[])
    (extraRefs : Array Cell := #[]) : Cell :=
  mkCodeCell (#[0xdb, 0x3e] ++ tailBytes) (#[target] ++ extraRefs)

private def targetRet : Cell :=
  mkCodeCell #[0xdb, 0x30]

private def targetPush1Ret : Cell :=
  mkCodeCell #[0x71, 0xdb, 0x30]

private def targetPush2Ret : Cell :=
  mkCodeCell #[0x72, 0xdb, 0x30]

private def noiseLeaf : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[]

private def noiseBranch : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[noiseLeaf]

private def noiseSlice : Slice :=
  Slice.ofCell noiseBranch

private def emptySlice : Slice :=
  Slice.ofCell Cell.empty

private def q0 : Value :=
  .cont (.quit 0)

private def tailPush3 : Array Nat :=
  #[0x73]

private def tailAdd : Array Nat :=
  #[0xa0]

private def tailRetAlt : Array Nat :=
  #[0xdb, 0x31]

private def branchObservableCode : Cell :=
  mkJmprefdataCodeCell targetPush1Ret tailPush3

private def noTailCode : Cell :=
  mkJmprefdataCodeCell targetRet #[]

private def altTargetCode : Cell :=
  mkJmprefdataCodeCell targetPush2Ret #[]

private def tailAddSkippedCode : Cell :=
  mkJmprefdataCodeCell targetPush1Ret tailAdd

private def tailRetAltSkippedCode : Cell :=
  mkJmprefdataCodeCell targetPush1Ret tailRetAlt

private def extraRefsCode : Cell :=
  mkJmprefdataCodeCellWithExtraRefs targetPush1Ret tailPush3 #[noiseLeaf]

private def specialTargetCell : Cell :=
  { bits := natToBits 2 8 ++ Array.replicate 256 false
    refs := #[]
    special := true
    levelMask := 0 }

private def specialBranchCode : Cell :=
  mkJmprefdataCodeCell specialTargetCell tailPush3

private def specialNoTailCode : Cell :=
  mkJmprefdataCodeCell specialTargetCell #[]

private def specialWithAddTailCode : Cell :=
  mkJmprefdataCodeCell specialTargetCell tailAdd

private def specialWithRetAltTailCode : Cell :=
  mkJmprefdataCodeCell specialTargetCell tailRetAlt

private def missingRefCode : Cell :=
  mkCodeCell #[0xdb, 0x3e] #[]

private def missingRefWithTailCode : Cell :=
  mkCodeCell (#[0xdb, 0x3e] ++ tailPush3) #[]

private def truncated8Code : Cell :=
  mkCodeCell #[0xdb] #[targetRet]

private def truncated15Code : Cell :=
  Cell.mkOrdinary ((natToBits jmprefdataOpcode 16).take 15) #[targetRet]

private def runJmprefdataDirect
    (target : Cell)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowJmpRef (jmprefdataInstr target) stack

private def runJmprefdataDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowJmpRef instr (VM.push (intV dispatchSentinel)) stack

private def runJmprefdataRaw
    (target : Cell)
    (stack : Array Value)
    (cc : Continuation := .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty)
    (loaded : Array (Array UInt8) := #[])
    (gas : GasLimits := GasLimits.default) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      loadedCells := loaded
      gas := gas }
  (execInstrFlowJmpRef (jmprefdataInstr target) (pure ())).run st0

private def sameSlice (a b : Slice) : Bool :=
  a.bitPos == b.bitPos && a.refPos == b.refPos && a.cell == b.cell

private def regsEq (x y : Regs) : Bool :=
  x.c0 == y.c0 && x.c1 == y.c1 && x.c2 == y.c2 && x.c3 == y.c3 &&
  x.c4 == y.c4 && x.c5 == y.c5 && x.c7 == y.c7

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

private def expectDecodeOkJmprefdata
    (label : String)
    (code : Cell)
    (expectedTarget : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (.jmpRefData s, bits, rest) =>
      if bits != 16 then
        throw (IO.userError s!"{label}: expected decoded bits=16, got {bits}")
      else if !(sameSlice s (Slice.ofCell expectedTarget)) then
        throw (IO.userError s!"{label}: decoded target mismatch")
      else if rest.refPos != 1 then
        throw (IO.userError s!"{label}: expected decoded refPos=1, got {rest.refPos}")
      else
        pure ()
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected JMPREFDATA, got instr={reprStr instr}, bits={bits}")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (code : Cell := branchObservableCode)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := jmprefdataId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def jmprefdataOracleFamilies : Array String :=
  #[
    "ok/branch/",
    "ok/no-tail/",
    "ok/alt-target/",
    "ok/tail-add-",
    "ok/tail-retalt-",
    "ok/extra-refs/",
    "special/cellund/",
    "decode/missing-ref/",
    "decode/truncated-",
    "decode/empty-code/"
  ]

private def jmprefdataFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := jmprefdataOracleFamilies
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

private def jmprefdataNoisePool : Array (Array Value) :=
  #[#[], #[intV 1], #[.null], #[.cell noiseBranch], #[.slice noiseSlice], #[.builder Builder.empty], #[q0]]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genJmprefdataFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (noise, rng2) := pickFromPool jmprefdataNoisePool rng1
  let case0 :=
    if shape = 0 then
      mkCase "fuzz/ok/branch" noise branchObservableCode
    else if shape = 1 then
      mkCase "fuzz/ok/no-tail" noise noTailCode
    else if shape = 2 then
      mkCase "fuzz/ok/alt-target" #[intV 6] altTargetCode
    else if shape = 3 then
      mkCase "fuzz/ok/extra-refs" noise extraRefsCode
    else if shape = 4 then
      mkCase "fuzz/err/special" noise specialBranchCode
    else if shape = 5 then
      mkCase "fuzz/err/decode/missing-ref" noise missingRefCode
    else if shape = 6 then
      mkCase "fuzz/err/decode/missing-ref-with-tail" noise missingRefWithTailCode
    else if shape = 7 then
      mkCase "fuzz/err/decode/truncated-8" noise truncated8Code
    else if shape = 8 then
      mkCase "fuzz/err/decode/truncated-15" noise truncated15Code
    else
      mkCase "fuzz/err/decode/empty-code" noise Cell.empty
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := jmprefdataId
  unit := #[
    { name := "unit/raw/pushcode-before-jump-and-cc-update"
      run := do
        let restCell := mkCodeCell tailPush3 #[noiseLeaf]
        let restSlice := Slice.ofCell restCell
        let base : VmState := VmState.initial Cell.empty
        let regsCustom : Regs :=
          { base.regs with c0 := .quit 30, c1 := .quit 31, c2 := .quit 32, c3 := .quit 33 }
        let ccRest : Continuation := .ordinary restSlice (.quit 17) OrdCregs.empty OrdCdata.empty
        let st0 : VmState :=
          { base with stack := #[intV 42], cc := ccRest, regs := regsCustom }
        let (res, st1) := (execInstrFlowJmpRef (jmprefdataInstr targetPush1Ret) (pure ())).run st0
        match res with
        | .error e =>
            throw (IO.userError s!"pushcode-jump: expected success, got {e}")
        | .ok _ =>
            let expectedCc : Continuation :=
              .ordinary (Slice.ofCell targetPush1Ret) (.quit 0) OrdCregs.empty OrdCdata.empty
            if st1.stack != #[intV 42, .slice restSlice] then
              throw (IO.userError s!"pushcode-jump: stack mismatch {reprStr st1.stack}")
            else if st1.cc != expectedCc then
              throw (IO.userError s!"pushcode-jump: cc mismatch {reprStr st1.cc}")
            else if st1.loadedCells.size != 1 then
              throw (IO.userError s!"pushcode-jump: expected loadedCells=1, got {st1.loadedCells.size}")
            else if !(regsEq st1.regs regsCustom) then
              throw (IO.userError s!"pushcode-jump: regs changed {reprStr st1.regs}")
            else
              pure () }
    ,
    { name := "unit/raw/special-rejected-before-pushcode"
      run := do
        let restSlice := Slice.ofCell (mkCodeCell tailPush3 #[noiseLeaf])
        let ccRest : Continuation := .ordinary restSlice (.quit 19) OrdCregs.empty OrdCdata.empty
        let (res, st1) := runJmprefdataRaw specialTargetCell #[intV 7] ccRest
        match res with
        | .error .cellUnd =>
            if st1.stack != #[intV 7] then
              throw (IO.userError s!"special-order: stack changed {reprStr st1.stack}")
            else if st1.cc != ccRest then
              throw (IO.userError s!"special-order: cc changed {reprStr st1.cc}")
            else if st1.loadedCells.size != 1 then
              throw (IO.userError s!"special-order: expected loadedCells=1, got {st1.loadedCells.size}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"special-order: expected cellUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "special-order: expected cellUnd, got success") }
    ,
    { name := "unit/raw/outofgas-before-pushcode"
      run := do
        let restSlice := Slice.ofCell (mkCodeCell tailPush3 #[noiseLeaf])
        let ccRest : Continuation := .ordinary restSlice (.quit 23) OrdCregs.empty OrdCdata.empty
        let tight : GasLimits := GasLimits.ofLimit 99
        let (res, st1) := runJmprefdataRaw targetPush1Ret #[intV 5] ccRest #[] tight
        match res with
        | .error .outOfGas =>
            if st1.stack != #[intV 5] then
              throw (IO.userError s!"oom-order: stack changed {reprStr st1.stack}")
            else if st1.cc != ccRest then
              throw (IO.userError s!"oom-order: cc changed {reprStr st1.cc}")
            else if st1.loadedCells.size != 1 then
              throw (IO.userError s!"oom-order: expected loadedCells=1, got {st1.loadedCells.size}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"oom-order: expected outOfGas, got {e}")
        | .ok _ =>
            throw (IO.userError "oom-order: expected outOfGas, got success") }
    ,
    { name := "unit/decode/success-and-ref-guard-errors"
      run := do
        expectDecodeOkJmprefdata "decode/ok" (mkJmprefdataCodeCell targetRet tailPush3) targetRet
        expectDecodeErr "decode/missing-ref" missingRefCode .invOpcode
        expectDecodeErr "decode/missing-ref-with-tail" missingRefWithTailCode .invOpcode
        expectDecodeErr "decode/truncated-8" truncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" truncated15Code .invOpcode
        expectDecodeErr "decode/empty" Cell.empty .invOpcode }
    ,
    { name := "unit/dispatch/fallback-and-match"
      run := do
        expectOkStack "dispatch/fallback"
          (runJmprefdataDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/match"
          (runJmprefdataDispatchFallback (jmprefdataInstr targetRet) #[intV 3])
          #[intV 3, .slice emptySlice] }
    ,
    { name := "unit/raw/reload-does-not-grow-loaded-set"
      run := do
        let restSlice := Slice.ofCell (mkCodeCell tailPush3 #[noiseLeaf])
        let ccRest : Continuation := .ordinary restSlice (.quit 29) OrdCregs.empty OrdCdata.empty
        let preloaded : Array (Array UInt8) := #[Cell.hashBytes targetPush1Ret]
        let (res, st1) := runJmprefdataRaw targetPush1Ret #[intV 11] ccRest preloaded
        match res with
        | .error e =>
            throw (IO.userError s!"reload: expected success, got {e}")
        | .ok _ =>
            if st1.stack != #[intV 11, .slice restSlice] then
              throw (IO.userError s!"reload: stack mismatch {reprStr st1.stack}")
            else if st1.loadedCells.size != 1 then
              throw (IO.userError s!"reload: expected loadedCells=1, got {st1.loadedCells.size}")
            else
              pure () }
    ,
    { name := "unit/raw/nonordinary-cc-typechk-at-pushcode"
      run := do
        let (res, st1) := runJmprefdataRaw targetRet #[intV 8] (.quit 44)
        match res with
        | .error .typeChk =>
            if st1.stack != #[intV 8] then
              throw (IO.userError s!"typechk-nonordinary-cc: stack changed {reprStr st1.stack}")
            else if st1.cc != .quit 44 then
              throw (IO.userError s!"typechk-nonordinary-cc: cc changed {reprStr st1.cc}")
            else if st1.loadedCells.size != 1 then
              throw (IO.userError s!"typechk-nonordinary-cc: expected loadedCells=1, got {st1.loadedCells.size}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"typechk-nonordinary-cc: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "typechk-nonordinary-cc: expected typeChk, got success") }
    ,
    { name := "unit/direct/no-stack-pop"
      run := do
        expectOkStack "direct/no-stack-pop"
          (runJmprefdataDirect targetRet #[.null, intV 9])
          #[.null, intV 9, .slice emptySlice] }
  ]
  oracle := #[
    mkCase "ok/branch/empty-stack" #[] branchObservableCode,
    mkCase "ok/branch/one-int" #[intV 5] branchObservableCode,
    mkCase "ok/branch/deep-two-ints" #[intV 2, intV 3] branchObservableCode,
    mkCase "ok/branch/deep-null-int" #[.null, intV 9] branchObservableCode,
    mkCase "ok/branch/deep-cell-tuple" #[.cell noiseBranch, .tuple #[]] branchObservableCode,
    mkCase "ok/branch/deep-slice" #[.slice noiseSlice, intV 1] branchObservableCode,
    mkCase "ok/branch/deep-builder" #[.builder Builder.empty, intV (-7)] branchObservableCode,
    mkCase "ok/branch/deep-cont" #[q0, intV 12] branchObservableCode,
    mkCase "ok/branch/max-int257" #[intV maxInt257] branchObservableCode,
    mkCase "ok/branch/min-plus1-int257" #[intV (minInt257 + 1)] branchObservableCode,

    mkCase "ok/no-tail/empty-stack" #[] noTailCode,
    mkCase "ok/no-tail/deep-null" #[.null, intV 8] noTailCode,
    mkCase "ok/no-tail/large-pos" #[intV (pow2 200)] noTailCode,
    mkCase "ok/no-tail/large-neg" #[intV (-(pow2 200))] noTailCode,

    mkCase "ok/alt-target/push2" #[intV 6] altTargetCode,
    mkCase "ok/tail-add-skipped" #[intV 2, intV 3] tailAddSkippedCode,
    mkCase "ok/tail-retalt-skipped" #[.null] tailRetAltSkippedCode,

    mkCase "ok/extra-refs/empty-stack" #[] extraRefsCode,
    mkCase "ok/extra-refs/deep-stack" #[.null, .tuple #[], intV 4] extraRefsCode,
    mkCase "ok/extra-refs/large-int" #[intV (pow2 255)] extraRefsCode,

    mkCase "special/cellund/empty-stack" #[] specialBranchCode,
    mkCase "special/cellund/deep-null-int" #[.null, intV 1] specialBranchCode,
    mkCase "special/cellund/deep-cell" #[.cell noiseBranch, intV 2] specialBranchCode,
    mkCase "special/cellund/deep-slice" #[.slice noiseSlice, intV 3] specialBranchCode,
    mkCase "special/cellund/deep-builder" #[.builder Builder.empty, intV 4] specialBranchCode,
    mkCase "special/cellund/deep-tuple" #[.tuple #[], intV 5] specialBranchCode,
    mkCase "special/cellund/deep-cont" #[q0, intV 6] specialBranchCode,
    mkCase "special/cellund/max-int257" #[intV maxInt257] specialBranchCode,
    mkCase "special/cellund/min-plus1-int257" #[intV (minInt257 + 1)] specialBranchCode,
    mkCase "special/cellund/no-tail" #[] specialNoTailCode,
    mkCase "special/cellund/with-tail-add" #[intV 2, intV 3] specialWithAddTailCode,
    mkCase "special/cellund/with-tail-retalt" #[.null] specialWithRetAltTailCode,

    mkCase "decode/missing-ref/empty-stack" #[] missingRefCode,
    mkCase "decode/missing-ref/int" #[intV 0] missingRefCode,
    mkCase "decode/missing-ref/deep-stack" #[.tuple #[], intV 1] missingRefCode,
    mkCase "decode/missing-ref/with-tail-empty" #[] missingRefWithTailCode,
    mkCase "decode/missing-ref/with-tail-int" #[intV 2] missingRefWithTailCode,
    mkCase "decode/missing-ref/with-tail-deep" #[.null, intV 3] missingRefWithTailCode,
    mkCase "decode/truncated-8bit-prefix" #[] truncated8Code,
    mkCase "decode/truncated-8bit-with-stack" #[intV 4] truncated8Code,
    mkCase "decode/truncated-15bit-prefix" #[] truncated15Code,
    mkCase "decode/truncated-15bit-with-stack" #[.null, intV 5] truncated15Code,
    mkCase "decode/empty-code/empty-stack" #[] Cell.empty,
    mkCase "decode/empty-code/with-stack" #[intV 6] Cell.empty
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr jmprefdataId
      count := 500
      gen := genJmprefdataFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.JMPREFDATA
