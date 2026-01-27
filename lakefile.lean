import Lake
open Lake DSL

package "tvm-lean" where
  version := v!"0.1.0"

lean_lib «TvmLean» where
  -- add library configuration options here

@[default_target]
lean_exe "tvm-lean" where
  root := `Main

lean_exe "tvm-lean-tests" where
  root := `Tests
