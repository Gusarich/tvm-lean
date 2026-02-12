import Std
import TvmLean
import TvmLean.Spec.Index

open TvmLean

namespace Tests

structure UnitCase where
  name : String
  run : IO Unit

structure OracleInitCregs where
  c0 : Option Continuation := none
  c1 : Option Continuation := none
  c2 : Option Continuation := none
  c3 : Option Continuation := none
  c4 : Option Cell := none
  c5 : Option Cell := none
  deriving Repr

structure OracleGasLimits where
  gasLimit : Int := 1_000_000
  gasMax : Int := 1_000_000
  gasCredit : Int := 0
  deriving Repr

structure OracleCase where
  name : String
  instr : InstrId
  program : Array Instr := #[]
  /-- Optional pre-assembled cp0 code cell (used for instructions with inline refs/consts that `assembleCp0` rejects). -/
  codeCell? : Option Cell := none
  initStack : Array Value := #[]
  initCregs : OracleInitCregs := {}
  initC7 : Array Value := #[]
  /-- Optional library collection cells used by `XLOAD{Q}` (mirrors C++ `VmState.libraries`). -/
  initLibraries : Array Cell := #[]
  gasLimits : OracleGasLimits := {}
  fuel : Nat := 1_000_000
  deriving Repr

structure ContMutationProfile where
  /-- Optional case-name prefixes to select branch families from oracle seeds. -/
  oracleNamePrefixes : Array String := #[]
  /-- Mutation mode weights. Modes: 0=drop, 1=top-replacement, 2=swap/dup, 3=noise, 4=int-perturb. -/
  mutationModes : Array Nat := #[0, 1, 2, 3, 4]
  /-- Inclusive bounds for number of stack-mutation steps. -/
  minMutations : Nat := 1
  maxMutations : Nat := 4
  /-- Include `err/*` seeds when selecting oracle bases. -/
  includeErrOracleSeeds : Bool := false
  deriving Repr

structure FuzzSpec where
  seed : UInt64
  count : Nat
  gen : StdGen → OracleCase × StdGen
  replayOracle : Bool := false
  mutateOracle : Bool := false
  contProfile : ContMutationProfile := {}

structure InstrSuite where
  id : InstrId
  unit : Array UnitCase := #[]
  oracle : Array OracleCase := #[]
  fuzz : Array FuzzSpec := #[]

initialize instrSuiteRegistry : IO.Ref (Array InstrSuite) ← IO.mkRef #[]

def registerSuite (suite : InstrSuite) : IO Unit := do
  instrSuiteRegistry.modify (·.push suite)

def registeredSuites : IO (Array InstrSuite) :=
  instrSuiteRegistry.get

private def foldHashBytes (h : UInt64) (bytes : Array UInt8) : UInt64 :=
  bytes.foldl (fun acc b => (acc ^^^ (UInt64.ofNat b.toNat)) * 1099511628211) h

/-- Deterministic per-instruction seed using FNV-1a over instruction name bytes. -/
def fuzzSeedForInstr (instr : InstrId) : UInt64 :=
  foldHashBytes 14695981039346656037 instr.name.toUTF8.data

/--
Build a fuzz spec that replays random oracle cases from the same suite.
This is branch-aware because continuation suites already encode branch maps in oracle pools.
-/
def mkReplayOracleFuzzSpec (instr : InstrId) (count : Nat := 500) : FuzzSpec :=
  { seed := fuzzSeedForInstr instr
    count := count
    gen := fun rng => ({ name := "fuzz/replay/placeholder", instr := instr }, rng)
    replayOracle := true }

/--
Build a fuzz spec that mutates oracle cases from the same suite.
Used by continuation suites that need stack-shape mutation instead of replay-only sampling.
-/
def mkContMutationFuzzSpec (instr : InstrId) (count : Nat := 500) : FuzzSpec :=
  { seed := fuzzSeedForInstr instr
    count := count
    gen := fun rng => ({ name := "fuzz/mutate/placeholder", instr := instr }, rng)
    mutateOracle := true }

/--
Build a mutation fuzz spec with an explicit instruction-local profile.
Use this for handcrafted continuation generators per instruction.
-/
def mkContMutationFuzzSpecWithProfile
    (instr : InstrId)
    (profile : ContMutationProfile)
    (count : Nat := 500) : FuzzSpec :=
  { seed := fuzzSeedForInstr instr
    count := count
    gen := fun rng => ({ name := "fuzz/mutate/placeholder", instr := instr }, rng)
    mutateOracle := true
    contProfile := profile }

end Tests
