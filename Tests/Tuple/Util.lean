import Tests.Registry

open TvmLean Tests

namespace Tests.Tuple

def runInstrWithStack (i : Instr) (stack : Stack) (fuel : Nat := 80) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [i] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let base : VmState := VmState.initial codeCell
  let st0 : VmState := { base with stack := stack }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError s!"{i.pretty}: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def vInt (n : Int) : Value := .int (.num n)

def mkTuple (xs : List Value) : Value :=
  .tuple xs.toArray

def assertExitOk (label : String) (code : Int) : IO Unit := do
  assert (code == -1) s!"{label}: unexpected exitCode={code}"

def assertExitExc (label : String) (code : Int) (e : Excno) : IO Unit := do
  assert (code == (~~~ e.toInt)) s!"{label}: expected {reprStr e}, got exitCode={code}"

end Tests.Tuple

