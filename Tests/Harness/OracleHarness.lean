import Tests.Harness.Registry
import TvmLean.Native
import TvmLean.Validation.Oracle.Runner

open TvmLean

namespace Tests

structure OracleRunResult where
  caseName : String
  instr : InstrId
  ok : Bool
  error? : Option String := none
  deriving Repr

private def assembleCaseCode (c : OracleCase) : Except String Cell := do
  let codeCell ←
    match assembleCp0 c.program.toList with
    | .ok cell => pure cell
    | .error e => throw s!"assembleCp0 failed: {reprStr e}"
  pure codeCell

private def toBocHex (c : Cell) : Except String String := do
  let bytes ←
    match stdBocSerialize c with
    | .ok b => pure b
    | .error e => throw s!"stdBocSerialize failed: {reprStr e}"
  pure (TvmLeanOracleValidate.bytesToHex bytes)

private def valueToToken (v : Value) : Except String String := do
  match v with
  | .int (.num n) => pure (toString n)
  | .int .nan => throw "cannot encode NaN in oracle stack token stream"
  | .null => pure "N"
  | .cell c =>
      let hex ← toBocHex c
      pure s!"CB:{hex}"
  | .slice s =>
      if s.bitPos = 0 && s.refPos = 0 && s.bitsRemaining = s.cell.bits.size && s.refsRemaining = s.cell.refs.size then
        let hex ← toBocHex s.cell
        pure s!"SB:{hex}"
      else
        throw "only full-cell slices are supported in oracle stack token stream"
  | .builder b =>
      if b.bits.isEmpty && b.refs.isEmpty then
        pure "B"
      else
        throw "non-empty builders are not yet supported in oracle stack token stream"
  | .tuple t =>
      if t.isEmpty then
        pure "T"
      else
        throw "non-empty tuples are not yet supported in oracle stack token stream"
  | .cont (.quit 0) => pure "K"
  | .cont _ => throw "only quit(0) continuations are supported in oracle stack token stream"

private def stackToTokens (stack : Array Value) : Except String (List String) := do
  let mut out : List String := []
  for v in stack do
    let tok ← valueToToken v
    out := out.concat tok
  pure out

private def leanExitGas (res : StepResult) : Except String (Int × Int) := do
  match res with
  | .halt exitCode stF =>
      pure (~~~ exitCode, stF.gas.gasConsumed)
  | .continue _ =>
      throw "Lean execution did not halt within fuel"

/--
  Executes a single case on Lean and on Fift `runvmx`, then compares exit code and gas.
-/
def runOracleCase (c : OracleCase) : IO OracleRunResult := do
  let codeCell ←
    match assembleCaseCode c with
    | .ok code => pure code
    | .error e =>
        return { caseName := c.name, instr := c.instr, ok := false, error? := some e }

  let stackTokens ←
    match stackToTokens c.initStack with
    | .ok toks => pure toks
    | .error e =>
        return { caseName := c.name, instr := c.instr, ok := false, error? := some e }

  let leanRes := TvmLeanOracleValidate.runLean codeCell c.initStack c.fuel
  let (leanExit, leanGas) ←
    match leanExitGas leanRes with
    | .ok x => pure x
    | .error e =>
        return { caseName := c.name, instr := c.instr, ok := false, error? := some e }

  let oracleRes : Except String TvmLeanOracleValidate.OracleOut ←
    try
      pure (Except.ok (← TvmLeanOracleValidate.runOracle codeCell stackTokens))
    catch e =>
      pure (Except.error s!"oracle run failed: {e.toString}")
  let oracleOut ←
    match oracleRes with
    | Except.ok out => pure out
    | Except.error e =>
        return { caseName := c.name, instr := c.instr, ok := false, error? := some e }

  if leanExit != oracleOut.exitRaw then
    return {
      caseName := c.name
      instr := c.instr
      ok := false
      error? := some s!"EXIT mismatch: lean={leanExit} oracle={oracleOut.exitRaw}"
    }
  if leanGas != oracleOut.gasUsed then
    return {
      caseName := c.name
      instr := c.instr
      ok := false
      error? := some s!"GAS mismatch: lean={leanGas} oracle={oracleOut.gasUsed}"
    }
  pure { caseName := c.name, instr := c.instr, ok := true }

end Tests
