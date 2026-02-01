import Tests.All
import Tests.Registry

def main (_args : List String) : IO Unit := do
  Tests.runRoundtrips
  Tests.runTests
  IO.println "ok"
