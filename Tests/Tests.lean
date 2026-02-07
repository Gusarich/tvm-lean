import Tests.Harness.Registry
import Tests.Harness.OracleHarness
import Tests.Harness.FuzzHarness
import Tests.Harness.Runner
import Tests.Harness.Cli
import Tests.Harness.Coverage
import Tests.All

namespace Tests

-- Keep this module "real" so Lake retains transitive import link artifacts.
initialize testRootLinked : IO.Ref Nat ← IO.mkRef 0

end Tests
