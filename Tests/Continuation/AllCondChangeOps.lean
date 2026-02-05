import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.CondChange

def runProgWithStack (prog : List Instr) (stack : Stack) (fuel : Nat := 120) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 prog with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let base : VmState := VmState.initial codeCell
  let st0 : VmState := { base with stack := stack }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError s!"prog: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def runCodeCellWithStack (codeCell : Cell) (stack : Stack) (fuel : Nat := 120) : IO (Int × VmState) := do
  let base : VmState := VmState.initial codeCell
  let st0 : VmState := { base with stack := stack }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError s!"cell: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def vInt (n : Int) : Value := .int (.num n)

def assertExitOk (ctx : String) (code : Int) : IO Unit := do
  assert (code == -1) s!"{ctx}: unexpected exitCode={code}"

def assertExitOkOrAlt (ctx : String) (code : Int) : IO Unit := do
  assert (code == -1 ∨ code == -2) s!"{ctx}: unexpected exitCode={code}"

def assertExitExc (ctx : String) (exc : Excno) (code : Int) : IO Unit := do
  let expected : Int := ~~~ exc.toInt
  assert (code == expected) s!"{ctx}: expected exitCode={expected}, got {code}"

def testCondAndChangeOps : IO Unit := do
  -- CONDSEL
  let (c1, st1) ← runProgWithStack [ .contExt .condSel ] #[vInt 1, vInt 10, vInt 20]
  assertExitOk "condsel(true)" c1
  assert (st1.stack == #[vInt 10]) s!"condsel(true): expected [10], got {st1.stack}"
  let (c0, st0) ← runProgWithStack [ .contExt .condSel ] #[vInt 0, vInt 10, vInt 20]
  assertExitOk "condsel(false)" c0
  assert (st0.stack == #[vInt 20]) s!"condsel(false): expected [20], got {st0.stack}"

  -- CONDSELCHK
  let (c2, st2) ← runProgWithStack [ .contExt .condSelChk ] #[vInt (-1), vInt 7, vInt 9]
  assertExitOk "condselchk(ok)" c2
  assert (st2.stack == #[vInt 7]) s!"condselchk(ok): expected [7], got {st2.stack}"
  let (c3, _) ← runProgWithStack [ .contExt .condSelChk ] #[vInt 1, vInt 7, .null]
  assertExitExc "condselchk(type-mismatch)" .typeChk c3

  -- IFRETALT / IFNOTRETALT (set c1 := c0 to keep exitCode -1 on taken branch)
  let (c4, st4) ← runProgWithStack [ .sameAlt, .contExt .ifretAlt, .pushInt (.num 999) ] #[vInt 1]
  assertExitOk "ifretalt(taken)" c4
  assert (st4.stack.isEmpty) s!"ifretalt(taken): expected empty stack"
  let (c5, st5) ← runProgWithStack [ .sameAlt, .contExt .ifretAlt, .pushInt (.num 999) ] #[vInt 0]
  assertExitOk "ifretalt(not-taken)" c5
  assert (st5.stack == #[vInt 999]) s!"ifretalt(not-taken): expected [999], got {st5.stack}"
  let (c6, st6) ← runProgWithStack [ .sameAlt, .contExt .ifnotretAlt, .pushInt (.num 999) ] #[vInt 0]
  assertExitOk "ifnotretalt(taken)" c6
  assert (st6.stack.isEmpty) s!"ifnotretalt(taken): expected empty stack"

  -- IFBITJMP / IFNBITJMP
  let bodyCell ←
    match assembleCp0 [ .pushInt (.num 1), .add ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let bodySlice : Slice := Slice.ofCell bodyCell
  let bodyCont : Continuation := .ordinary bodySlice (.quit 0) OrdCregs.empty OrdCdata.empty
  let (c7, st7) ← runProgWithStack [ .contExt (.ifbitjmp 3), .pushInt (.num 999) ] #[vInt 8, .cont bodyCont]
  assertExitOk "ifbitjmp(taken)" c7
  assert (st7.stack == #[vInt 9]) s!"ifbitjmp(taken): expected [9], got {st7.stack}"
  let (c8, st8) ← runProgWithStack [ .contExt (.ifbitjmp 2), .pushInt (.num 999) ] #[vInt 8, .cont bodyCont]
  assertExitOk "ifbitjmp(not-taken)" c8
  assert (st8.stack == #[vInt 8, vInt 999]) s!"ifbitjmp(not-taken): expected [8,999], got {st8.stack}"
  let (c9, st9) ← runProgWithStack [ .contExt (.ifnbitjmp 2), .pushInt (.num 999) ] #[vInt 8, .cont bodyCont]
  assertExitOk "ifnbitjmp(taken)" c9
  assert (st9.stack == #[vInt 9]) s!"ifnbitjmp(taken): expected [9], got {st9.stack}"

  -- IFBITJMPREF / IFNBITJMPREF (handcrafted code cell; assembler can't emit refs)
  let bsPush8 ←
    match encodeCp0 (.pushInt (.num 8)) with
    | .ok bs => pure bs
    | .error e => throw (IO.userError s!"encodeCp0 failed: {reprStr e}")
  let bsPush999 ←
    match encodeCp0 (.pushInt (.num 999)) with
    | .ok bs => pure bs
    | .error e => throw (IO.userError s!"encodeCp0 failed: {reprStr e}")
  let bitsIfBitRef : BitString := natToBits ((0x71e <<< 5) + 3) 16
  let codeIfBitRef : Cell := Cell.mkOrdinary (bsPush8 ++ bitsIfBitRef ++ bsPush999) #[bodyCell]
  let (c10, st10) ← runCodeCellWithStack codeIfBitRef #[] 160
  assertExitOk "ifbitjmpref(taken)" c10
  assert (st10.stack == #[vInt 9]) s!"ifbitjmpref(taken): expected [9], got {st10.stack}"

  let bitsIfNBitRef : BitString := natToBits ((0x71f <<< 5) + 2) 16
  let codeIfNBitRef : Cell := Cell.mkOrdinary (bsPush8 ++ bitsIfNBitRef ++ bsPush999) #[bodyCell]
  let (c11, st11) ← runCodeCellWithStack codeIfNBitRef #[] 160
  assertExitOk "ifnbitjmpref(taken)" c11
  assert (st11.stack == #[vInt 9]) s!"ifnbitjmpref(taken): expected [9], got {st11.stack}"

  -- ATEXIT: execute the provided continuation on normal exit.
  let exitCell ←
    match assembleCp0 [ .pushInt (.num 5) ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let exitSlice : Slice := Slice.ofCell exitCell
  let exitCont : Continuation := .ordinary exitSlice (.quit 0) OrdCregs.empty OrdCdata.empty
  let (c12, st12) ← runProgWithStack [ .contExt .atexit ] #[.cont exitCont] 160
  assertExitOk "atexit(exec-on-exit)" c12
  assert (st12.stack == #[vInt 5]) s!"atexit: expected [5], got {st12.stack}"

  -- ATEXITALT: structural check that c1 becomes a composed continuation.
  let (c13, st13) ← runProgWithStack [ .contExt .atexitAlt, .pushCtr 1 ] #[.cont exitCont] 80
  assertExitOk "atexitalt(pushctr1)" c13
  assert (st13.stack.size == 1) s!"atexitalt: expected 1 stack item"
  match st13.stack[0]! with
  | .cont (.ordinary _ _ cregs _) =>
      assert (cregs.c1 == some (.quit 1)) s!"atexitalt: expected saved c1=quit1"
  | v => throw (IO.userError s!"atexitalt: expected cont, got {v.pretty}")

  -- THENRET / THENRETALT: computed composed continuation on stack.
  let (c14, st14) ← runProgWithStack [ .contExt .thenret ] #[.cont exitCont] 80
  assertExitOk "thenret" c14
  match st14.stack.get? 0 with
  | some (.cont (.ordinary _ _ cregs _)) =>
      assert (cregs.c0 == some (.quit 0)) s!"thenret: expected saved c0=quit0"
  | some v => throw (IO.userError s!"thenret: expected cont, got {v.pretty}")
  | none => throw (IO.userError "thenret: empty stack")

  let (c15, st15) ← runProgWithStack [ .contExt .thenretAlt ] #[.cont exitCont] 80
  assertExitOk "thenretalt" c15
  match st15.stack.get? 0 with
  | some (.cont (.ordinary _ _ cregs _)) =>
      assert (cregs.c0 == some (.quit 1)) s!"thenretalt: expected saved c0=quit1"
  | some v => throw (IO.userError s!"thenretalt: expected cont, got {v.pretty}")
  | none => throw (IO.userError "thenretalt: empty stack")

  -- INVERT: swap c0 and c1.
  let (c16, st16) ← runProgWithStack [ .contExt .invert, .pushCtr 0, .pushCtr 1 ] #[] 40
  assertExitOkOrAlt "invert" c16
  assert (st16.stack.size == 2) s!"invert: expected 2 stack items"
  match st16.stack[0]!, st16.stack[1]! with
  | .cont (.quit 1), .cont (.quit 0) => pure ()
  | v0, v1 => throw (IO.userError s!"invert: unexpected stack [{v0.pretty}, {v1.pretty}]")

  -- BOOLEVAL: normal return pushes -1, alt return pushes 0.
  let emptyCell ←
    match assembleCp0 [] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let emptySlice : Slice := Slice.ofCell emptyCell
  let normalCont : Continuation := .ordinary emptySlice (.quit 0) OrdCregs.empty OrdCdata.empty
  let (c17, st17) ← runProgWithStack [ .contExt .booleval ] #[.cont normalCont] 160
  assertExitOk "booleval(normal)" c17
  assert (st17.stack == #[vInt (-1)]) s!"booleval(normal): expected [-1], got {st17.stack}"

  let altCell ←
    match assembleCp0 [ .retAlt ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let altSlice : Slice := Slice.ofCell altCell
  let altCont : Continuation := .ordinary altSlice (.quit 0) OrdCregs.empty OrdCdata.empty
  let (c18, st18) ← runProgWithStack [ .contExt .booleval ] #[.cont altCont] 200
  assertExitOk "booleval(alt)" c18
  assert (st18.stack == #[vInt 0]) s!"booleval(alt): expected [0], got {st18.stack}"

initialize
  Tests.registerTest "continuation/cond-change" testCondAndChangeOps
  Tests.registerRoundtrip (.contExt .condSel)
  Tests.registerRoundtrip (.contExt .condSelChk)
  Tests.registerRoundtrip (.contExt .ifretAlt)
  Tests.registerRoundtrip (.contExt .ifnotretAlt)
  Tests.registerRoundtrip (.contExt (.ifbitjmp 0))
  Tests.registerRoundtrip (.contExt (.ifnbitjmp 31))
  Tests.registerRoundtrip (.contExt .atexit)
  Tests.registerRoundtrip (.contExt .atexitAlt)
  Tests.registerRoundtrip (.contExt .thenret)
  Tests.registerRoundtrip (.contExt .thenretAlt)
  Tests.registerRoundtrip (.contExt .invert)
  Tests.registerRoundtrip (.contExt .booleval)

end Tests.Continuation.CondChange
