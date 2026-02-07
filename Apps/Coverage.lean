import Tests.Harness.Coverage

namespace TvmLeanCoverageApp

inductive OutputFormat where
  | json
  | md
  | tsv
  deriving Repr, DecidableEq

structure CliOpts where
  format : OutputFormat := .json
  outPath? : Option System.FilePath := none
  deriving Repr

partial def parseArgs (args : List String) (opts : CliOpts := {}) : IO CliOpts :=
  match args with
  | [] => pure opts
  | "--format" :: "json" :: rest =>
      parseArgs rest { opts with format := .json }
  | "--format" :: "md" :: rest =>
      parseArgs rest { opts with format := .md }
  | "--format" :: "tsv" :: rest =>
      parseArgs rest { opts with format := .tsv }
  | "--out" :: path :: rest =>
      parseArgs rest { opts with outPath? := some path }
  | "--" :: rest =>
      parseArgs rest opts
  | arg :: _ =>
      throw (IO.userError s!"unknown argument: {arg}")

def render (format : OutputFormat) (report : TvmLean.CoverageReport) : String :=
  match format with
  | .json => Tests.coverageAsJson report
  | .md => Tests.coverageAsMarkdown report
  | .tsv => Tests.coverageAsTsv report

def main (args : List String) : IO UInt32 := do
  let opts ← parseArgs args
  let report ← Tests.generateCoverageReport
  let out := render opts.format report
  match opts.outPath? with
  | some p => IO.FS.writeFile p out
  | none => IO.println out
  pure 0

end TvmLeanCoverageApp

def main (args : List String) : IO UInt32 :=
  TvmLeanCoverageApp.main args
