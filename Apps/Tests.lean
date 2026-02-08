import Tests.All
import Tests.Harness.Cli
import Tests.Harness.Runner

namespace TvmLeanTestsApp

def main (args : List String) : IO UInt32 := do
  let opts ← Tests.parseCliArgs args
  Tests.runAndReport opts

end TvmLeanTestsApp

def main (args : List String) : IO UInt32 :=
  TvmLeanTestsApp.main args
