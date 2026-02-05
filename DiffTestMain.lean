import TvmLean.DiffTest

open TvmLean
open Lean

structure CliOpts where
  casePath? : Option System.FilePath := none
  dirPath? : Option System.FilePath := none
  maxCases : Nat := 0
  progressEvery : Nat := 0
  shard : Nat := 0
  shards : Nat := 1
  fuel : Nat := 1_000_000
  gasLimit : Int := 1_000_000
  skipUnsupported : Bool := false
  strictExit : Bool := false
  traceFailures : Bool := false
  traceAll : Bool := false
  traceMax : Nat := 200
  outPath? : Option System.FilePath := none
  deriving Repr

partial def parseArgs (args : List String) (opts : CliOpts := {}) : IO CliOpts :=
  match args with
  | [] => pure opts
  | "--case" :: path :: rest =>
      parseArgs rest { opts with casePath? := some path }
  | "--dir" :: path :: rest =>
      parseArgs rest { opts with dirPath? := some path }
  | "--max-cases" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { opts with maxCases := v }
      | none => throw (IO.userError s!"invalid --max-cases {n}")
  | "--progress" :: rest =>
      parseArgs rest { opts with progressEvery := (if opts.progressEvery > 0 then opts.progressEvery else 100) }
  | "--progress-every" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { opts with progressEvery := v }
      | none => throw (IO.userError s!"invalid --progress-every {n}")
  | "--shard" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { opts with shard := v }
      | none => throw (IO.userError s!"invalid --shard {n}")
  | "--shards" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { opts with shards := v }
      | none => throw (IO.userError s!"invalid --shards {n}")
  | "--fuel" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { opts with fuel := v }
      | none => throw (IO.userError s!"invalid --fuel {n}")
  | "--gas-limit" :: n :: rest =>
      match n.toInt? with
      | some v => parseArgs rest { opts with gasLimit := v }
      | none => throw (IO.userError s!"invalid --gas-limit {n}")
  | "--skip-unsupported" :: rest =>
      parseArgs rest { opts with skipUnsupported := true }
  | "--strict-exit" :: rest =>
      parseArgs rest { opts with strictExit := true }
  | "--trace-failures" :: rest =>
      parseArgs rest { opts with traceFailures := true }
  | "--trace-all" :: rest =>
      parseArgs rest { opts with traceAll := true }
  | "--trace-max" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { opts with traceMax := v }
      | none => throw (IO.userError s!"invalid --trace-max {n}")
  | "--out" :: path :: rest =>
      parseArgs rest { opts with outPath? := some path }
  | "--" :: rest =>
      parseArgs rest opts
  | arg :: _ =>
      throw (IO.userError s!"unknown argument: {arg}")

def writeReport (path : System.FilePath) (results : Array TestResult) : IO Unit := do
  let json := Json.arr (results.map ToJson.toJson)
  IO.FS.writeFile path (json.pretty)

def runOne (opts : CliOpts) (path : System.FilePath) : IO TestResult := do
  let tc ← loadTestCase path
  runTestCase
    { fuel := opts.fuel
      gasLimit := opts.gasLimit
      skipUnsupported := opts.skipUnsupported
      traceFailures := opts.traceFailures
      traceAll := opts.traceAll
      traceMax := opts.traceMax } tc

def hasHiddenSegment (p : System.FilePath) : Bool :=
  let parts := (toString p).split fun c => c = '/' || c = '\\'
  parts.any fun seg => seg.startsWith "_"

def isJsonFile (p : System.FilePath) : Bool :=
  match p.fileName with
  | some name => p.extension == some "json" && !name.startsWith "_" && !hasHiddenSegment p
  | none => false

def percentStr (num denom : Nat) : String :=
  if denom = 0 then
    "0.00%"
  else
    let bp : Nat := num * 10000 / denom
    let whole : Nat := bp / 100
    let frac : Nat := bp % 100
    let fracStr := if frac < 10 then s!"0{frac}" else toString frac
    s!"{whole}.{fracStr}%"

def main (args : List String) : IO Unit := do
  let opts ← parseArgs args
  let mut results : Array TestResult := #[]

  if opts.shards = 0 then
    throw (IO.userError "invalid --shards 0")
  if opts.shard ≥ opts.shards then
    throw (IO.userError s!"invalid shard index: --shard {opts.shard} must be < --shards {opts.shards}")

  match opts.casePath?, opts.dirPath? with
  | some casePath, none =>
      let r ← runOne opts casePath
      results := results.push r
  | none, some dirPath =>
      let files ← dirPath.walkDir
      let jsonFiles := (files.filter isJsonFile).qsort (fun a b => toString a < toString b)
      let shardedFiles :=
        if opts.shards = 1 then
          jsonFiles
        else
          Id.run do
            let mut out : Array System.FilePath := #[]
            for i in [0:jsonFiles.size] do
              if i % opts.shards = opts.shard then
                out := out.push jsonFiles[i]!
            return out

      let totalAll := shardedFiles.size
      let total :=
        if opts.maxCases > 0 then
          Nat.min opts.maxCases totalAll
        else
          totalAll

      let mut i : Nat := 0
      let mut pass : Nat := 0
      let mut fail : Nat := 0
      let mut skip : Nat := 0
      let mut err : Nat := 0

      while i < total do
        let f := shardedFiles[i]!
        let r ← runOne opts f
        results := results.push r
        match r.status with
        | .pass => pass := pass + 1
        | .fail => fail := fail + 1
        | .skip => skip := skip + 1
        | .error => err := err + 1

        i := i + 1
        if opts.progressEvery > 0 && (i % opts.progressEvery = 0 || i = total) then
          let passPct := percentStr pass i
          IO.println s!"progress: {i}/{total} pass={pass} fail={fail} skip={skip} error={err} pass%={passPct}"
  | some _, some _ =>
      throw (IO.userError "use only one of --case or --dir")
  | none, none =>
      throw (IO.userError "missing required argument: --case <file.json> or --dir <dir>")

  let pass := results.foldl (fun acc r => if r.status == .pass then acc + 1 else acc) 0
  let fail := results.foldl (fun acc r => if r.status == .fail then acc + 1 else acc) 0
  let skip := results.foldl (fun acc r => if r.status == .skip then acc + 1 else acc) 0
  let err := results.foldl (fun acc r => if r.status == .error then acc + 1 else acc) 0

  IO.println s!"total={results.size} pass={pass} fail={fail} skip={skip} error={err}"

  match opts.outPath? with
  | some outPath => writeReport outPath results
  | none => pure ()

  if opts.strictExit && (fail > 0 || skip > 0 || err > 0) then
    IO.Process.exit 1
  else
    pure ()
