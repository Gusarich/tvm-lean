-- Auto-generated stub for TVM instruction QLSHIFT_VAR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQlshiftVar : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 5), .arithExt (.lshiftVar true) ])
  expectExitOk "qlshift_var(1,5)" exitCode1
  assert (st1.stack.size == 1) s!"qlshift_var(1,5): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 32) s!"qlshift_var(1,5): expected 32, got {n}"
  | v => throw (IO.userError s!"qlshift_var(1,5): unexpected stack value {v.pretty}")

  -- overflow is quiet
  let (exitCodeOv, stOv) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 256), .arithExt (.lshiftVar true) ])
  expectExitOk "qlshift_var(1,256)" exitCodeOv
  assert (stOv.stack.size == 1) s!"qlshift_var(1,256): unexpected stack size={stOv.stack.size}"
  match stOv.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"qlshift_var(1,256): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/qlshift_var" testQlshiftVar
  Tests.registerRoundtrip (.arithExt (.lshiftVar true))
