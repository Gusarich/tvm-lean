import Tests.Harness.Runner

namespace Tests

partial def parseCliArgs (args : List String) (opts : RunnerOpts := {}) : IO RunnerOpts :=
  match args with
  | [] => pure opts
  | "--filter" :: id :: rest =>
      parseCliArgs rest { opts with filter? := some id }
  | "--unit-only" :: rest =>
      parseCliArgs rest { opts with unitOnly := true }
  | "--oracle-only" :: rest =>
      parseCliArgs rest { opts with oracleOnly := true }
  | "--fuzz-only" :: rest =>
      parseCliArgs rest { opts with fuzzOnly := true }
  | "--" :: rest =>
      parseCliArgs rest opts
  | arg :: _ =>
      throw (IO.userError s!"unknown argument: {arg}")

end Tests
