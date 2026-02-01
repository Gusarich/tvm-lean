import Tests.Util

open TvmLean

namespace Tests

abbrev NamedTest := String × IO Unit

initialize testRegistry : IO.Ref (Array NamedTest) ← IO.mkRef #[]

def registerTest (name : String) (t : IO Unit) : IO Unit := do
  testRegistry.modify (·.push (name, t))

initialize roundtripRegistry : IO.Ref (Array Instr) ← IO.mkRef #[]

def registerRoundtrip (i : Instr) : IO Unit := do
  roundtripRegistry.modify (·.push i)

def runRoundtrips : IO Unit := do
  for i in (← roundtripRegistry.get) do
    roundtrip i

def runTests : IO Unit := do
  for (name, t) in (← testRegistry.get) do
    try
      t
    catch e =>
      throw (IO.userError s!"{name}: {e.toString}")

end Tests

