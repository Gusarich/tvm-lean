-- Auto-generated stub for TVM instruction SETGLOB (category: globals).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testGlobalsSetGlob : IO Unit := do
  let base : Array Value := #[.int (.num 0)]

  let (code0, st0) ← runInstrWithC7 (.tonEnvOp (.setGlob 3)) base (stack := #[.int (.num 123)])
  assert (code0 == -1) s!"SETGLOB: unexpected exitCode={code0}"
  assert (st0.stack.isEmpty) s!"SETGLOB: expected empty stack, got size={st0.stack.size}"
  assert (st0.regs.c7.size == 4) s!"SETGLOB: expected c7 size 4, got {st0.regs.c7.size}"
  assert (st0.regs.c7[3]! == .int (.num 123)) s!"SETGLOB: unexpected c7[3]={st0.regs.c7[3]!.pretty}"

initialize
  Tests.registerTest "globals/setglob" testGlobalsSetGlob
  Tests.registerRoundtrip (.tonEnvOp (.setGlob 1))
  Tests.registerRoundtrip (.tonEnvOp (.setGlob 31))
