import Tests.Harness.Registry
import TvmLean.Native
import TvmLean.Validation.Canon.Result
import TvmLean.Validation.Oracle.Report
import TvmLean.Validation.Oracle.Runner

open TvmLean

namespace Tests

structure OracleRunResult where
  caseName : String
  instr : InstrId
  ok : Bool
  comparison? : Option OracleComparison := none
  error? : Option String := none
  deriving Repr

private def assembleCaseCode (c : OracleCase) : Except String Cell := do
  match c.codeCell? with
  | some codeCell => pure codeCell
  | none =>
      match assembleCp0 c.program.toList with
      | .ok cell => pure cell
      | .error e => throw s!"assembleCp0 failed: {reprStr e}"

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
        let hex ← toBocHex b.finalize
        pure s!"BB:{hex}"
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

private def applyInitCregs (regs : Regs) (init : OracleInitCregs) : Regs :=
  { c0 := init.c0.getD regs.c0
    c1 := init.c1.getD regs.c1
    c2 := init.c2.getD regs.c2
    c3 := init.c3.getD regs.c3
    c4 := init.c4.getD regs.c4
    c5 := init.c5.getD regs.c5
    c7 := regs.c7 }

private def oracleSeedState (code : Cell) (initStack : Array Value) : VmState :=
  match TvmLeanOracleValidate.runLean code initStack 0 with
  | .halt _ st => st
  | .continue st => st

private def runLeanCase (code : Cell) (c : OracleCase) : StepResult :=
  let seed := oracleSeedState code c.initStack
  let regs0 := applyInitCregs seed.regs c.initCregs
  let regs :=
    if c.initC7.isEmpty then
      regs0
    else
      { regs0 with c7 := c.initC7 }
  let st0 :=
    { seed with
      stack := c.initStack
      regs := regs
      libraries := c.initLibraries
      gas := GasLimits.ofLimits c.gasLimits.gasLimit c.gasLimits.gasMax c.gasLimits.gasCredit }
  VmState.run nativeHost c.fuel st0

private def leanCanonResult (res : StepResult) : Except String CanonResult := do
  match res with
  | .halt exitCode stF =>
      let (c4Out, c5Out) := TvmLeanOracleValidate.leanOutCells stF
      pure (CanonResult.ofLeanState (~~~ exitCode) stF.gas.gasConsumed c4Out c5Out stF.stack)
  | .continue _ =>
      throw "Lean execution did not halt within fuel"

private def oracleCanonResult (out : TvmLeanOracleValidate.OracleOut) : CanonResult :=
  CanonResult.ofOracleRaw out.exitRaw out.gasUsed out.c4Hash out.c5Hash out.stackTop

/--
  Executes a single case on Lean and on Fift `runvmx`, then compares full canonical results.
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

  let leanCanon ←
    match leanCanonResult (runLeanCase codeCell c) with
    | .ok result => pure result
    | .error e =>
        return { caseName := c.name, instr := c.instr, ok := false, error? := some e }

  let oracleRes : Except String TvmLeanOracleValidate.OracleOut ←
    try
      pure (Except.ok (← TvmLeanOracleValidate.runOracle codeCell stackTokens c.initLibraries))
    catch e =>
      pure (Except.error s!"oracle run failed: {e.toString}")
  let oracleOut ←
    match oracleRes with
    | .ok out => pure out
    | .error e =>
        return { caseName := c.name, instr := c.instr, ok := false, error? := some e }

  let oracleCanon := oracleCanonResult oracleOut
  let cmp := compareCanonResults leanCanon oracleCanon
  if cmp.ok then
    pure { caseName := c.name, instr := c.instr, ok := true, comparison? := some cmp }
  else
    let msg :=
      match cmp.mismatch? with
      | some mismatch => mismatch.message
      | none => "oracle comparison failed"
    pure
      { caseName := c.name
        instr := c.instr
        ok := false
        comparison? := some cmp
        error? := some msg }

end Tests
