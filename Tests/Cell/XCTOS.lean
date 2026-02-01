-- Auto-generated stub for TVM instruction XCTOS (category: cell).
import Tests.Registry

open TvmLean Tests

def testXctosIsSpecial : IO Unit := do
  let codeCell ←
    match assembleCp0 [ .xctos ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let base := VmState.initial codeCell

  -- Ordinary cell → is_special=false (0)
  let ordinary : Cell := cellOfBytes #[0xaa]
  let st0Ord : VmState := { base with stack := #[.cell ordinary] }
  match VmState.run 20 st0Ord with
  | .continue _ => throw (IO.userError "xctos(ordinary): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"xctos(ordinary): unexpected exitCode={exitCode}"
      assert (st.stack.size == 2) s!"xctos(ordinary): expected stack size=2, got {st.stack.size}"
      match st.stack[0]!, st.stack[1]! with
      | .slice _, .int (.num n) => assert (n == 0) s!"xctos(ordinary): expected 0, got {n}"
      | a, b => throw (IO.userError s!"xctos(ordinary): unexpected stack [{a.pretty}, {b.pretty}]")

  -- Library exotic cell → is_special=true (-1)
  let hashBytes : Array UInt8 := Array.replicate 32 0
  let libOrd : Cell := cellOfBytes (#[UInt8.ofNat 2] ++ hashBytes)
  let lib : Cell := { libOrd with special := true, levelMask := 0 }
  let st0Lib : VmState := { base with stack := #[.cell lib] }
  match VmState.run 20 st0Lib with
  | .continue _ => throw (IO.userError "xctos(library): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"xctos(library): unexpected exitCode={exitCode}"
      assert (st.stack.size == 2) s!"xctos(library): expected stack size=2, got {st.stack.size}"
      match st.stack[0]!, st.stack[1]! with
      | .slice _, .int (.num n) => assert (n == -1) s!"xctos(library): expected -1, got {n}"
      | a, b => throw (IO.userError s!"xctos(library): unexpected stack [{a.pretty}, {b.pretty}]")

initialize
  Tests.registerTest "cell/xctos_is_special" testXctosIsSpecial
  Tests.registerRoundtrip (.xctos)
