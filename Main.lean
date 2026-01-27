import TvmLean

structure CliOpts where
  trace : Bool := false
  fuel : Nat := 100
  bocPath? : Option String := none
  c4 : Nat := 41
  deriving Repr

partial def parseArgs (args : List String) (opts : CliOpts := {}) : IO CliOpts :=
  match args with
  | [] => pure opts
  | "--trace" :: rest =>
      parseArgs rest { opts with trace := true }
  | "--fuel" :: n :: rest =>
      match n.toNat? with
      | some fuel => parseArgs rest { opts with fuel := fuel }
      | none => throw (IO.userError s!"invalid --fuel {n}")
  | "--boc" :: path :: rest =>
      parseArgs rest { opts with bocPath? := some path }
  | "--c4" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { opts with c4 := v }
      | none => throw (IO.userError s!"invalid --c4 {n}")
  | "--" :: rest =>
      parseArgs rest opts
  | arg :: _ =>
      throw (IO.userError s!"unknown argument: {arg}")

def runWithTrace (fuel : Nat) (st : TvmLean.VmState) : IO TvmLean.StepResult := do
  match fuel with
  | 0 =>
      pure (.halt (TvmLean.Excno.fatal.toInt) st)
  | fuel + 1 =>
      let next :=
        match st.cc with
        | .ordinary code =>
            if code.bitsRemaining == 0 then
              if code.refsRemaining == 0 then
                "<implicit RET>"
              else
                "<implicit JMPREF>"
            else if st.cp = 0 then
              match TvmLean.decodeCp0 code with
              | .ok (i, _) => reprStr i
              | .error e => s!"<decode error {reprStr e}>"
            else
              s!"<cp={st.cp}>"
        | .quit n =>
            s!"<quit {n}>"
        | .excQuit =>
            "<excQuit>"
      IO.println s!"gas={st.gas.gasRemaining} next={next} stack={TvmLean.Stack.pretty st.stack}"
      let r := st.step
      match r with
      | .continue st' => runWithTrace fuel st'
      | .halt _ _ => pure r

def main (args : List String) : IO Unit := do
  let opts ← parseArgs args

  let prog : List TvmLean.Instr :=
    [ .pushCtr 4
    , .ctos
    , .ldu 32
    , .ends
    , .inc
    , .newc
    , .stu 32
    , .endc
    , .popCtr 4
    ]
  let codeCell : TvmLean.Cell ←
    match opts.bocPath? with
    | some path =>
        let bytes ← IO.FS.readBinFile path
        match TvmLean.stdBocDeserialize bytes with
        | .ok c => pure c
        | .error e => throw (IO.userError s!"BOC parse error: {e}")
    | none =>
        match TvmLean.assembleCp0 prog with
        | .ok c => pure c
        | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let initC4 : TvmLean.Cell := TvmLean.Cell.ofUInt 32 opts.c4
  let st0 : TvmLean.VmState :=
    { (TvmLean.VmState.initial codeCell) with regs := { (TvmLean.Regs.initial) with c4 := initC4 } }
  let res ←
    if opts.trace then
      runWithTrace opts.fuel st0
    else
      pure (TvmLean.VmState.run opts.fuel st0)
  match res with
  | .halt exitCode st => do
      IO.println s!"exitCode={exitCode}"
      IO.println s!"stack={TvmLean.Stack.pretty st.stack}"
      IO.println s!"c4(bits={st.regs.c4.bits.size})={TvmLean.bitsToNat st.regs.c4.bits}"
  | .continue _ => do
      IO.println "did not halt (fuel exhausted?)"
