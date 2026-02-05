import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.JmpRef

def runCodeCellWith (codeCell : Cell) (stack : Stack := #[]) (fuel : Nat := 120) : IO (Int × VmState) := do
  let base : VmState := VmState.initial codeCell
  let st0 : VmState := { base with stack := stack }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError "code cell: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def vInt (n : Int) : Value := .int (.num n)

def assertExitOk (ctx : String) (code : Int) : IO Unit := do
  assert (code == -1) s!"{ctx}: unexpected exitCode={code}"

def testJmpRefOps : IO Unit := do
  let refCell : Cell := Cell.mkOrdinary #[] #[]

  -- JMPREF: execute a ref jump; with empty ref code it immediately RETs to c0 (quit0) => halt ok.
  let codeJmpRef : Cell := Cell.mkOrdinary (natToBits 0xdb3d 16) #[refCell]
  let (codeJR, stJR) ← runCodeCellWith codeJmpRef #[vInt 1, vInt 2]
  assertExitOk "flow/jmpref" codeJR
  assert (stJR.stack == #[vInt 1, vInt 2]) s!"flow/jmpref: stack changed unexpectedly"

  -- JMPREFDATA: pushes the remaining code slice (after the jump instruction), then jumps.
  let bs99 ←
    match encodeCp0 (.pushInt (.num 99)) with
    | .ok bs => pure bs
    | .error e => throw (IO.userError s!"encodeCp0(pushInt 99) failed: {reprStr e}")
  let codeJmpRefData : Cell := Cell.mkOrdinary (natToBits 0xdb3e 16 ++ bs99) #[refCell]
  let (codeJRD, stJRD) ← runCodeCellWith codeJmpRefData #[]
  assertExitOk "flow/jmprefdata" codeJRD
  assert (stJRD.stack.size == 1) s!"flow/jmprefdata: expected stack size 1"
  match stJRD.stack[0]! with
  | .slice s =>
      match decodeCp0WithBits s with
      | .ok (instr, _, _) =>
          assert (instr == .pushInt (.num 99)) s!"flow/jmprefdata: expected pushed code to start with PUSHINT 99, got {instr.pretty}"
      | .error e =>
          throw (IO.userError s!"flow/jmprefdata: decode failed: {reprStr e}")
  | v => throw (IO.userError s!"flow/jmprefdata: expected slice, got {v.pretty}")

initialize
  Tests.registerTest "continuation/jmpref" testJmpRefOps

end Tests.Continuation.JmpRef

