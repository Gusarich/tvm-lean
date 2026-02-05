import Tests.Registry

open TvmLean Tests

namespace Tests.Stack

def runInstrWithStack (i : Instr) (stack : Stack) (fuel : Nat := 50) : IO (Int × VmState) := do
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

def stackPretty (s : Stack) : String :=
  let elems := s.toList.map (fun v => v.pretty)
  "[" ++ String.intercalate ", " elems ++ "]"

def assertStackEq (ctx : String) (got expect : Stack) : IO Unit := do
  assert (got.size == expect.size) s!"{ctx}: stack size mismatch got={got.size} expect={expect.size} got={stackPretty got} expect={stackPretty expect}"
  for i in [0:got.size] do
    assert (got[i]! == expect[i]!) s!"{ctx}: stack[{i}] mismatch got={got[i]!.pretty} expect={expect[i]!.pretty} got={stackPretty got} expect={stackPretty expect}"

end Tests.Stack

