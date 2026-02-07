import Tests.Harness.Registry
import Tests.Harness.OracleHarness
import Tests.Harness.FuzzHarness
import Tests.Harness.Runner
import Tests.Harness.Cli
import Tests.Harness.Coverage

namespace Tests

-- Keep this module "real" so Lake retains test harness link artifacts.
initialize testRootLinked : IO.Ref Nat ← IO.mkRef 0

end Tests
