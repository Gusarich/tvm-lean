import Tests.Harness.Runner

namespace Tests

private def parsePositiveNatArg (flag : String) (value : String) : IO Nat :=
  match value.trim.toNat? with
  | some n =>
      if n > 0 then
        pure n
      else
        throw (IO.userError s!"{flag}: expected positive integer, got {value}")
  | none =>
      throw (IO.userError s!"{flag}: expected positive integer, got {value}")

partial def parseCliArgs (args : List String) (opts : RunnerOpts := {}) : IO RunnerOpts :=
  match args with
  | [] => pure opts
  | "--filter" :: id :: rest =>
      parseCliArgs rest { opts with filter? := some id }
  | "--jobs" :: n :: rest => do
      let jobs ← parsePositiveNatArg "--jobs" n
      parseCliArgs rest { opts with jobs? := some jobs }
  | "--no-progress" :: rest =>
      parseCliArgs rest { opts with progress := false }
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
