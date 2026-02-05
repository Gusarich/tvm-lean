import Tests.Registry

open TvmLean Tests

namespace Tests.Dictionary

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

def runCodeCellWith (code : Cell) (stack : Stack := #[]) (fuel : Nat := 80) : IO (Int × VmState) := do
  let base : VmState := VmState.initial code
  let st0 : VmState := { base with stack := stack }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError "code cell: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def vInt (n : Int) : Value := .int (.num n)

def mkCellBits (bs : BitString) (refs : Array Cell := #[]) : Cell :=
  Cell.mkOrdinary bs refs

def mkSliceBits (bs : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (mkCellBits bs refs)

def mkKeySlice (keyBits : BitString) : Slice :=
  mkSliceBits keyBits

def sliceToCell (s : Slice) : Cell :=
  s.toCellRemaining

def stackPretty (s : Stack) : String :=
  let elems := s.toList.map (fun v => v.pretty)
  "[" ++ String.intercalate ", " elems ++ "]"

def assertStackEq (ctx : String) (got expect : Stack) : IO Unit := do
  assert (got.size == expect.size)
    s!"{ctx}: stack size mismatch got={got.size} expect={expect.size} got={stackPretty got} expect={stackPretty expect}"
  for i in [0:got.size] do
    assert (got[i]! == expect[i]!)
      s!"{ctx}: stack[{i}] mismatch got={got[i]!.pretty} expect={expect[i]!.pretty} got={stackPretty got} expect={stackPretty expect}"

def assertExitOk (ctx : String) (code : Int) : IO Unit := do
  assert (code == -1) s!"{ctx}: unexpected exitCode={code}"

def assertExitExc (ctx : String) (code : Int) (e : Excno) : IO Unit := do
  assert (code == (~~~ e.toInt)) s!"{ctx}: expected {reprStr e}, got exitCode={code}"

def dictKeyBitsOrFail (idx : Int) (n : Nat) (unsigned : Bool) : IO BitString := do
  match dictKeyBits? idx n unsigned with
  | some bs => pure bs
  | none => throw (IO.userError s!"dictKeyBits? failed: idx={idx} n={n} unsigned={unsigned}")

def mkDictRootSlice (entries : List (BitString × Slice)) : IO (Option Cell) := do
  let mut root? : Option Cell := none
  for (k, v) in entries do
    match dictSetSliceWithCells root? k v .set with
    | .ok (root2?, ok, _created, _loaded) =>
        if !ok then throw (IO.userError "mkDictRootSlice: dictSet returned ok=false for mode=set")
        root? := root2?
    | .error e => throw (IO.userError s!"mkDictRootSlice: {reprStr e}")
  pure root?

def mkDictRootRef (entries : List (BitString × Cell)) : IO (Option Cell) := do
  let mut root? : Option Cell := none
  for (k, v) in entries do
    match dictSetRefWithCells root? k v .set with
    | .ok (root2?, ok, _created, _loaded) =>
        if !ok then throw (IO.userError "mkDictRootRef: dictSet returned ok=false for mode=set")
        root? := root2?
    | .error e => throw (IO.userError s!"mkDictRootRef: {reprStr e}")
  pure root?

def mkDictRootBuilder (entries : List (BitString × Builder)) : IO (Option Cell) := do
  let mut root? : Option Cell := none
  for (k, v) in entries do
    match dictSetBuilderWithCells root? k v .set with
    | .ok (root2?, ok, _created, _loaded) =>
        if !ok then throw (IO.userError "mkDictRootBuilder: dictSet returned ok=false for mode=set")
        root? := root2?
    | .error e => throw (IO.userError s!"mkDictRootBuilder: {reprStr e}")
  pure root?

end Tests.Dictionary

