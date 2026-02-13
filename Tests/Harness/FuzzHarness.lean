import Lean
import Tests.Harness.Registry
import Tests.Harness.OracleHarness

namespace Tests

open Lean
open TvmLean

structure FuzzFailure where
  iteration : Nat
  result : OracleRunResult
  artifact? : Option System.FilePath := none
  deriving Repr

structure FuzzRunResult where
  seed : UInt64
  total : Nat
  failures : Array FuzzFailure
  artifacts : Array System.FilePath
  deriving Repr

private def sanitizeFileToken (s : String) : String :=
  String.map (fun c => if c.isAlphanum || c = '_' || c = '-' then c else '_') s

private def fuzzArtifactDir : IO System.FilePath := do
  let dir := (← IO.getEnv "TVMLEAN_FUZZ_FAILURE_DIR").getD "build/fuzz-failures"
  pure dir

private def oracleCaseJson (c : OracleCase) : Json :=
  Json.mkObj
    [ ("name", Json.str c.name)
    , ("instr", Json.str c.instr.name)
    , ("program", Json.str (reprStr c.program))
    , ("initStack", Json.str (reprStr c.initStack))
    , ("initCregs", Json.str (reprStr c.initCregs))
    , ("initC7", Json.str (reprStr c.initC7))
    , ("gasLimits", Json.mkObj
        [ ("gasLimit", ToJson.toJson c.gasLimits.gasLimit)
        , ("gasMax", ToJson.toJson c.gasLimits.gasMax)
        , ("gasCredit", ToJson.toJson c.gasLimits.gasCredit)
        ])
    , ("fuel", ToJson.toJson c.fuel)
    ]

private def dumpFailureArtifact
    (seed : UInt64)
    (iteration : Nat)
    (oracleCase : OracleCase)
    (runResult : OracleRunResult) : IO (Option System.FilePath) := do
  try
    let dir ← fuzzArtifactDir
    IO.FS.createDirAll dir
    let fileName :=
      s!"{sanitizeFileToken oracleCase.instr.name}_seed_{seed.toNat}_iter_{iteration}.json"
    let outPath := dir / fileName
    let body :=
      Json.mkObj
        [ ("instruction", Json.str oracleCase.instr.name)
        , ("seed", ToJson.toJson seed.toNat)
        , ("iteration", ToJson.toJson iteration)
        , ("case", oracleCaseJson oracleCase)
        , ("comparison",
            match runResult.comparison? with
            | some cmp => ToJson.toJson cmp
            | none => Json.null)
        , ("error",
            match runResult.error? with
            | some e => Json.str e
            | none => Json.null)
        ]
    IO.FS.writeFile outPath body.pretty
    pure (some outPath)
  catch _ =>
    pure none

private def replayCaseName (baseName : String) (iteration : Nat) (tag : Nat) : String :=
  s!"{baseName}/replay-{iteration}-{tag}"

private def isFullCellSlice (s : Slice) : Bool :=
  s.bitPos = 0
    && s.refPos = 0
    && s.bitsRemaining = s.cell.bits.size
    && s.refsRemaining = s.cell.refs.size

private def oracleTokenEncodable : Value → Bool
  | .int (.num _) => true
  | .int .nan => false
  | .null => true
  | .cell _ => true
  | .slice s => isFullCellSlice s
  | .builder _ => true
  | .tuple t => t.isEmpty
  | .cont (.quit 0) => true
  | .cont _ => false

private def normalizeOracleTokenValue : Value → Value
  | .int .nan => .int (.num 0)
  | .slice s =>
      if isFullCellSlice s then
        .slice s
      else
        .slice (Slice.ofCell s.cell)
  | .tuple _ => .tuple #[]
  | .cont _ => .cont (.quit 0)
  | v => v

private def normalizeOracleTokenStack (stack : Array Value) : Array Value :=
  stack.map normalizeOracleTokenValue

private def stackAllOracleTokenEncodable (stack : Array Value) : Bool :=
  stack.foldl (init := true) fun ok v => ok && oracleTokenEncodable v

private def randArrayElem? {α : Type} (xs : Array α) (rng : StdGen) : Option α × StdGen :=
  if xs.isEmpty then
    (none, rng)
  else
    let (idx, rng') := randNat rng 0 (xs.size - 1)
    (xs[idx]?, rng')

private def randSignedSmallInt (rng : StdGen) : Int × StdGen :=
  let (mag, rng1) := randNat rng 0 2048
  let (neg, rng2) := randBool rng1
  let n : Int := Int.ofNat mag
  (if neg && mag != 0 then -n else n, rng2)

private def valueKindTag (v : Value) : String :=
  match v with
  | .int _ => "int"
  | .null => "null"
  | .cell _ => "cell"
  | .slice _ => "slice"
  | .builder _ => "builder"
  | .tuple _ => "tuple0"
  | .cont _ => "quit0"

private def sampleOracleTokenValue (basis0 : Array Value) (rng : StdGen) : Value × String × StdGen :=
  let basis := normalizeOracleTokenStack basis0
  let cells :=
    basis.foldl (init := #[]) fun acc v =>
      match v with
      | .cell c => acc.push c
      | .slice s => acc.push s.cell
      | _ => acc
  let slices :=
    basis.foldl (init := #[]) fun acc v =>
      match v with
      | .slice s =>
          if isFullCellSlice s then
            acc.push s
          else
            acc
      | _ => acc
  let builders :=
    basis.foldl (init := #[]) fun acc v =>
      match v with
      | .builder b => acc.push b
      | _ => acc
  let (mode, rng1) := randNat rng 0 7
  match mode with
  | 0 =>
      let (n, rng2) := randSignedSmallInt rng1
      (.int (.num n), "int", rng2)
  | 1 =>
      (.null, "null", rng1)
  | 2 =>
      match randArrayElem? cells rng1 with
      | (some c, rng2) => (.cell c, "cell", rng2)
      | (none, rng2) => (.cell Cell.empty, "cell", rng2)
  | 3 =>
      match randArrayElem? slices rng1 with
      | (some s, rng2) => (.slice s, "slice", rng2)
      | (none, rng2) =>
          match randArrayElem? cells rng2 with
          | (some c, rng3) => (.slice (Slice.ofCell c), "slice", rng3)
          | (none, rng3) => (.slice (Slice.ofCell Cell.empty), "slice", rng3)
  | 4 =>
      match randArrayElem? builders rng1 with
      | (some b, rng2) => (.builder b, "builder", rng2)
      | (none, rng2) => (.builder Builder.empty, "builder", rng2)
  | 5 =>
      (.tuple #[], "tuple0", rng1)
  | 6 =>
      (.cont (.quit 0), "quit0", rng1)
  | _ =>
      match randArrayElem? basis rng1 with
      | (some v, rng2) =>
          let v' := normalizeOracleTokenValue v
          (v', s!"reuse-{valueKindTag v'}", rng2)
      | (none, rng2) =>
          (.int (.num 0), "int", rng2)

private def dropTopN (stack : Array Value) (n : Nat) : Array Value :=
  let keep := stack.size - Nat.min n stack.size
  stack.extract 0 keep

private def mutateDrop (stack : Array Value) (rng : StdGen) : Array Value × String × StdGen :=
  if stack.isEmpty then
    (stack, "drop0", rng)
  else
    let maxDrop := Nat.min 3 stack.size
    let (n, rng1) := randNat rng 1 maxDrop
    (dropTopN stack n, s!"drop{n}", rng1)

private def mutateTopReplacement (stack : Array Value) (rng : StdGen) : Array Value × String × StdGen :=
  let (v, vTag, rng1) := sampleOracleTokenValue stack rng
  if stack.isEmpty then
    (#[v], s!"top-add-{sanitizeFileToken vTag}", rng1)
  else
    let idx := stack.size - 1
    (stack.set! idx v, s!"top-repl-{sanitizeFileToken vTag}", rng1)

private def mutateSwapDup (stack : Array Value) (rng : StdGen) : Array Value × String × StdGen :=
  if 2 ≤ stack.size then
    let (doSwap, rng1) := randBool rng
    if doSwap then
      let topIdx := stack.size - 1
      let belowIdx := stack.size - 2
      match stack[topIdx]?, stack[belowIdx]? with
      | some topV, some belowV =>
          let stack1 := stack.set! topIdx belowV
          let stack2 := stack1.set! belowIdx topV
          (stack2, "swap", rng1)
      | _, _ =>
          (stack, "swap-noop", rng1)
    else
      match stack[stack.size - 1]? with
      | some topV => (stack.push topV, "dup", rng1)
      | none => (stack, "dup-noop", rng1)
  else if 1 = stack.size then
    match stack[0]? with
    | some topV => (stack.push topV, "dup", rng)
    | none => (stack, "dup-noop", rng)
  else
    let (v, vTag, rng1) := sampleOracleTokenValue stack rng
    (#[v], s!"dup-empty-{sanitizeFileToken vTag}", rng1)

private def sampleNoiseValues
    (basis : Array Value)
    (count : Nat)
    (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  let mut i : Nat := 0
  while i < count do
    let (v, _, rng') := sampleOracleTokenValue basis rng
    out := out.push v
    rng := rng'
    i := i + 1
  pure (out, rng)

private def mutateNoisePrefixSuffix (stack : Array Value) (rng : StdGen) : Array Value × String × StdGen :=
  let (count, rng1) := randNat rng 1 3
  let (asPrefix, rng2) := randBool rng1
  let (noise, rng3) := sampleNoiseValues stack count rng2
  if asPrefix then
    (noise ++ stack, s!"noise-prefix{count}", rng3)
  else
    (stack ++ noise, s!"noise-suffix{count}", rng3)

private def intPerturbDeltas : Array Int :=
  #[-16, -7, -3, -2, -1, 1, 2, 3, 7, 16]

private def oracleCliIntLimit : Int :=
  1_000_000_000_000_000_000

private def intSafeForOracleCli (n : Int) : Bool :=
  n.natAbs ≤ oracleCliIntLimit.natAbs

private def valueOracleCliCompatible (v : Value) : Bool :=
  oracleTokenEncodable v &&
    match v with
    | .int (.num n) => intSafeForOracleCli n
    | .int .nan => false
    | _ => true

private def stackOracleCliCompatible (stack : Array Value) : Bool :=
  stack.foldl (init := true) fun ok v => ok && valueOracleCliCompatible v

private def oracleCaseAsmCompatible (c : OracleCase) : Bool :=
  match c.codeCell? with
  | some _ => true
  | none =>
      match assembleCp0 c.program.toList with
      | .ok _ => true
      | .error _ => false

private def oracleCaseFuzzComparable (c : OracleCase) : Bool :=
  oracleCaseAsmCompatible c
    && stackOracleCliCompatible c.initStack
    && c.initC7.isEmpty

private def isSkippableFuzzOracleError (msg : String) : Bool :=
  msg.startsWith "assembleCp0 failed:"
    || msg.startsWith "cannot encode NaN in oracle stack token stream"
    || msg.startsWith "only full-cell slices are supported in oracle stack token stream"
    || msg.startsWith "non-empty tuples are not yet supported in oracle stack token stream"
    || msg.startsWith "only quit(0) continuations are supported in oracle stack token stream"
    || !((msg.splitOn "times:integer expected").tail.isEmpty)

private def intValueIndices (stack : Array Value) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for i in [0:stack.size] do
    match stack[i]? with
    | some (.int (.num _)) => out := out.push i
    | _ => pure ()
  pure out

private def mutateIntPerturbation (stack : Array Value) (rng : StdGen) : Array Value × String × StdGen :=
  let intIdxs := intValueIndices stack
  if intIdxs.isEmpty then
    let (n, rng1) := randSignedSmallInt rng
    (stack.push (.int (.num n)), "int-insert", rng1)
  else
    let (pickIdx, rng1) := randNat rng 0 (intIdxs.size - 1)
    match intIdxs[pickIdx]? with
    | some idx =>
        let (deltaIdx, rng2) := randNat rng1 0 (intPerturbDeltas.size - 1)
        match intPerturbDeltas[deltaIdx]?, stack[idx]? with
        | some delta, some (.int (.num n)) =>
            if intSafeForOracleCli n then
              let stack' := stack.set! idx (.int (.num (n + delta)))
              let deltaTag := sanitizeFileToken (toString delta)
              (stack', s!"int-perturb-{deltaTag}", rng2)
            else
              let (small, rng3) := randSignedSmallInt rng2
              let stack' := stack.set! idx (.int (.num small))
              (stack', "int-perturb-reseed-small", rng3)
        | _, _ =>
            (stack, "int-perturb-noop", rng2)
    | none =>
        (stack, "int-perturb-noop", rng1)

private def applyOneStackMutation
    (profile : ContMutationProfile)
    (stack : Array Value)
    (rng : StdGen) : Array Value × String × StdGen :=
  let modes :=
    if profile.mutationModes.isEmpty then
      #[0, 1, 2, 3, 4]
    else
      profile.mutationModes
  let (pick, rng1) := randNat rng 0 (modes.size - 1)
  let mode := modes[pick]!
  let mode := mode % 5
  match mode with
  | 0 => mutateDrop stack rng1
  | 1 => mutateTopReplacement stack rng1
  | 2 => mutateSwapDup stack rng1
  | 3 => mutateNoisePrefixSuffix stack rng1
  | _ => mutateIntPerturbation stack rng1

private def mutateOracleInitStack
    (profile : ContMutationProfile)
    (stack0 : Array Value)
    (rng0 : StdGen) : Array Value × Array String × StdGen := Id.run do
  let mut stack := normalizeOracleTokenStack stack0
  let mut tags : Array String := #[]
  let minSteps := max 1 profile.minMutations
  let maxSteps := max minSteps profile.maxMutations
  let (steps, rng1) := randNat rng0 minSteps maxSteps
  let mut rng := rng1
  let mut i : Nat := 0
  while i < steps do
    let (stack', tag, rng') := applyOneStackMutation profile stack rng
    stack := normalizeOracleTokenStack stack'
    tags := tags.push (sanitizeFileToken tag)
    rng := rng'
    i := i + 1
  if stackAllOracleTokenEncodable stack then
    pure (stack, tags, rng)
  else
    pure (normalizeOracleTokenStack stack, tags.push "normalize", rng)

private def mutationCaseName
    (baseName : String)
    (iteration : Nat)
    (tag : Nat)
    (mutationTags : Array String) : String :=
  let suffix :=
    if mutationTags.isEmpty then
      "mut"
    else
      "mut-" ++ String.intercalate "-" mutationTags.toList
  s!"{baseName}/{suffix}-{iteration}-{tag}"

private def oracleCaseMatchesAnyPrefix (prefixes : Array String) (name : String) : Bool :=
  prefixes.foldl (init := false) fun ok pfx => ok || name.startsWith pfx

private def oraclePoolByPrefixes
    (oraclePool : Array OracleCase)
    (prefixes : Array String) : Array OracleCase :=
  if prefixes.isEmpty then
    oraclePool
  else
    let filtered := oraclePool.filter (fun c => oracleCaseMatchesAnyPrefix prefixes c.name)
    if filtered.isEmpty then oraclePool else filtered

private def mutatableOraclePool
    (oraclePool : Array OracleCase)
    (profile : ContMutationProfile) : Array OracleCase :=
  let byPrefix := oraclePoolByPrefixes oraclePool profile.oracleNamePrefixes
  if profile.includeErrOracleSeeds then
    byPrefix
  else
    let preferred := byPrefix.filter (fun c => !c.name.startsWith "err/")
    if preferred.isEmpty then byPrefix else preferred

private def nextFuzzOracleCase
    (spec : FuzzSpec)
    (oraclePool : Array OracleCase)
    (iteration : Nat)
    (gen : StdGen) : OracleCase × StdGen :=
  if spec.mutateOracle then
    let pool := mutatableOraclePool oraclePool spec.contProfile
    if pool.isEmpty then
      spec.gen gen
    else
      let (idx, gen1) := randNat gen 0 (pool.size - 1)
      let (tag, gen2) := randNat gen1 0 999_999
      match pool[idx]? with
      | some oracleCase =>
          let (mutStack, mutTags, gen3) :=
            mutateOracleInitStack spec.contProfile oracleCase.initStack gen2
          ({ oracleCase with
              instr := oracleCase.instr
              initStack := mutStack
              name := mutationCaseName oracleCase.name iteration tag mutTags }, gen3)
      | none =>
          let (fallback, gen3) := spec.gen gen2
          let (mutStack, mutTags, gen4) :=
            mutateOracleInitStack spec.contProfile fallback.initStack gen3
          ({ fallback with
              initStack := mutStack
              name := mutationCaseName fallback.name iteration tag mutTags }, gen4)
  else if spec.replayOracle then
    if oraclePool.isEmpty then
      spec.gen gen
    else
      let (idx, gen1) := randNat gen 0 (oraclePool.size - 1)
      let (tag, gen2) := randNat gen1 0 999_999
      match oraclePool[idx]? with
      | some oracleCase =>
          ({ oracleCase with name := replayCaseName oracleCase.name iteration tag }, gen2)
      | none =>
          let (fallback, gen3) := spec.gen gen2
          ({ fallback with name := replayCaseName fallback.name iteration tag }, gen3)
  else
    spec.gen gen

def runFuzzSpec (spec : FuzzSpec) (oraclePool : Array OracleCase := #[]) : IO FuzzRunResult := do
  let mut gen := mkStdGen spec.seed.toNat
  let mut i : Nat := 0
  let mut attempts : Nat := 0
  let maxAttempts : Nat := spec.count.succ * 64
  let mut failures : Array FuzzFailure := #[]
  let mut artifacts : Array System.FilePath := #[]
  while i < spec.count && attempts < maxAttempts do
    attempts := attempts + 1
    let (oracleCase, gen') := nextFuzzOracleCase spec oraclePool i gen
    gen := gen'
    if !oracleCaseFuzzComparable oracleCase then
      continue
    let out ← runOracleCase oracleCase
    if !out.ok then
      match out.error? with
      | some msg =>
          if isSkippableFuzzOracleError msg then
            continue
      | none => pure ()
    i := i + 1
    if !out.ok then
      let artifact? ← dumpFailureArtifact spec.seed i oracleCase out
      failures := failures.push { iteration := i, result := out, artifact? := artifact? }
      match artifact? with
      | some p => artifacts := artifacts.push p
      | none => pure ()
    i := i + 1
  pure { seed := spec.seed, total := spec.count, failures := failures, artifacts := artifacts }

end Tests
