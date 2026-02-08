import Tests.Harness.Registry
import TvmLean.Spec.Index
import TvmLean.Semantics.Exec.Dispatch
import TvmLean.Native
import TvmLean.Validation.Coverage.Report

open TvmLean

namespace Tests

private def mkProbeCell (pfx : Nat) (checkLen : Nat) (skipLen : Nat) : Cell :=
  let argsLen : Nat := skipLen - checkLen
  let prefixLimit : Nat := (1 <<< checkLen)
  let pfxNorm : Nat :=
    if pfx < prefixLimit then
      pfx
    else
      pfx >>> argsLen
  let argsVal : Nat :=
    if pfx < prefixLimit then
      0
    else if argsLen = 0 then
      0
    else
      pfx &&& ((1 <<< argsLen) - 1)
  let padLen : Nat := Nat.min 512 (1023 - skipLen)
  let pad : BitString := Array.replicate padLen false
  let bits : BitString := natToBits pfxNorm checkLen ++ natToBits argsVal argsLen ++ pad
  let refs : Array Cell := Array.replicate 4 Cell.empty
  Cell.mkOrdinary bits refs

private def probeImplStatus (row : InstrSpecRow) : InstrImplStatus :=
  if row.checkLenBits = 0 || row.skipLenBits = 0 || row.checkLenBits > row.skipLenBits || row.skipLenBits > 1023 then
    .missing
  else
    let cell := mkProbeCell row.prefixBits row.checkLenBits row.skipLenBits
    match decodeCp0WithBits (Slice.ofCell cell) with
    | .error _ => .missing
    | .ok (instr, _totBits, _rest) =>
        let st0 := VmState.initial cell
        let (res, _st1) := (execInstr nativeHost instr).run st0
        match res with
        | .error .unimplemented => .stub
        | .error .invOpcode => .missing
        | .error .fatal => .broken
        | .error .unknown => .broken
        | .error .outOfGas => .broken
        -- Most instructions will fail our probe due to missing stack/environment;
        -- this still indicates they are decoded and have an execution path.
        | .error _ => .ok
        | .ok _ => .ok

private def countCasesFor (id : InstrId) (suites : Array InstrSuite) : Nat × Nat × Nat :=
  Id.run do
    let mut unitCount : Nat := 0
    let mut oracleCount : Nat := 0
    let mut fuzzCount : Nat := 0
    for suite in suites do
      if suite.id = id then
        unitCount := unitCount + suite.unit.size
        oracleCount := oracleCount + suite.oracle.size
        fuzzCount := fuzzCount + suite.fuzz.size
    return (unitCount, oracleCount, fuzzCount)

def generateCoverageReport : IO CoverageReport := do
  let suites ← registeredSuites
  let mut rows : Array InstrCoverageRow := #[]
  for specRow in allInstrRows do
    let (unitCount, oracleCount, fuzzCount) := countCasesFor specRow.id suites
    rows := rows.push
      { id := specRow.id
        impl := probeImplStatus specRow
        unitCases := unitCount
        oracleCases := oracleCount
        fuzzSpecs := fuzzCount }
  pure { rows := rows }

private def implStatusString : InstrImplStatus → String
  | .ok => "ok"
  | .stub => "stub"
  | .missing => "missing"
  | .broken => "broken"

def coverageAsTsv (report : CoverageReport) : String :=
  let header := "instr\timpl\tunit\toracle\tfuzz"
  let lines := report.rows.toList.map fun row =>
    s!"{row.id.name}\t{implStatusString row.impl}\t{row.unitCases}\t{row.oracleCases}\t{row.fuzzSpecs}"
  String.intercalate "\n" (header :: lines)

def coverageAsMarkdown (report : CoverageReport) : String :=
  let header := "| Instr | Impl | Unit | Oracle | Fuzz |"
  let sep := "|---|---|---:|---:|---:|"
  let lines := report.rows.toList.map fun row =>
    s!"| {row.id.name} | {implStatusString row.impl} | {row.unitCases} | {row.oracleCases} | {row.fuzzSpecs} |"
  String.intercalate "\n" (header :: sep :: lines)

def coverageAsJson (report : CoverageReport) : String :=
  let rowStrs := report.rows.toList.map fun row =>
    "{\"instr\":\"" ++ row.id.name
      ++ "\",\"impl\":\"" ++ implStatusString row.impl
      ++ "\",\"unit\":" ++ toString row.unitCases
      ++ ",\"oracle\":" ++ toString row.oracleCases
      ++ ",\"fuzz\":" ++ toString row.fuzzSpecs
      ++ "}"
  "[" ++ String.intercalate "," rowStrs ++ "]"

end Tests
