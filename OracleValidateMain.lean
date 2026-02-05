import Lean
import TvmLean

open TvmLean

namespace TvmLeanOracleValidate

def die (msg : String) : IO α :=
  throw <| IO.userError msg

def asObj (j : Lean.Json) : IO (List (String × Lean.Json)) :=
  match j with
  | .obj o => pure o.toList
  | _ => die "expected JSON object"

def asArr (j : Lean.Json) : IO (Array Lean.Json) :=
  match j with
  | .arr a => pure a
  | _ => die "expected JSON array"

def asStr (j : Lean.Json) : IO String :=
  match j with
  | .str s => pure s
  | _ => die "expected JSON string"

def asNat (j : Lean.Json) : IO Nat :=
  match j with
  | .num n => do
      if n.exponent != 0 then
        (die s!"expected Nat JSON number, got {n}" : IO Unit)
      else
        pure ()
      if n.mantissa < 0 then
        (die s!"expected Nat JSON number, got {n}" : IO Unit)
      else
        pure ()
      pure n.mantissa.toNat
  | _ => die "expected JSON number"

def findKey? (k : String) (xs : List (String × Lean.Json)) : Option Lean.Json :=
  xs.findSome? (fun (k', v) => if k' = k then some v else none)

def bytesToHex (bs : ByteArray) : String :=
  String.intercalate "" (bs.data.toList.map (fun b => natToHexPad b.toNat 2))

def hashHex (bs : Array UInt8) : String :=
  String.intercalate "" (bs.toList.map (fun b => natToHexPad b.toNat 2))

def canonContTy : Continuation → String
  | .ordinary .. => "vmc_std"
  | .envelope .. => "vmc_envelope"
  | .quit _ => "vmc_quit"
  | .excQuit => "vmc_quit_exc"
  | .whileCond .. => "vmc_while_cond"
  | .whileBody .. => "vmc_while_body"
  | .untilBody .. => "vmc_until"
  | .repeatBody .. => "vmc_repeat"
  | .againBody .. => "vmc_again"

partial def canonValue (v : Value) : String :=
  match v with
  | .null => "null"
  | .int .nan => "nan"
  | .int (.num n) => s!"int:{n}"
  | .cell c => s!"cell:{hashHex (Cell.hashBytes c)}"
  | .slice s => s!"slice:{hashHex (Cell.hashBytes s.toCellRemaining)}"
  | .builder b => s!"builder:{hashHex (Cell.hashBytes b.finalize)}"
  | .tuple t =>
      let inner := String.intercalate "," (t.toList.map canonValue)
      "tuple[" ++ toString t.size ++ "]{" ++ inner ++ "}"
  | .cont k => "cont:Cont{" ++ canonContTy k ++ "}"

def mkProbeCell (pfx : Nat) (checkLen : Nat) (skipLen : Nat) : Cell :=
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

structure InstrRow where
  name : String
  signature : String
  pfx : Nat
  checkLen : Nat
  skipLen : Nat
  deriving Repr

def parseRows (idx : Lean.Json) : IO (Array InstrRow) := do
  let top ← asObj idx
  let tvmJ ←
    match findKey? "tvm_instructions" top with
    | some j => pure j
    | none => die "missing tvm_instructions"
  let tvmArr ← asArr tvmJ
  let mut out : Array InstrRow := #[]
  for insJ in tvmArr do
    let insObj ← asObj insJ
    let name ←
      match findKey? "name" insObj with
      | some j => asStr j
      | none => die "missing instruction name"
    let signature :=
      match findKey? "signature_stack_string" insObj with
      | some (.str s) => s
      | _ => ""
    let layoutJ ←
      match findKey? "layout" insObj with
      | some j => pure j
      | none => die s!"missing layout for {name}"
    let layoutObj ← asObj layoutJ
    let pfx ←
      match findKey? "prefix" layoutObj with
      | some j => asNat j
      | none => pure 0
    let checkLen ←
      match findKey? "checkLen" layoutObj with
      | some j => asNat j
      | none => pure 0
    let skipLen ←
      match findKey? "skipLen" layoutObj with
      | some j => asNat j
      | none => pure 0
    out := out.push { name, signature, pfx, checkLen, skipLen }
  return out

def parseSigSideTypes (s : String) : List (String × String) :=
  let dropRightWhile (t : String) (p : Char → Bool) : String :=
    String.mk <| (t.data.reverse.dropWhile p).reverse
  let toks :=
    s.trim.split (fun c => c == ' ' || c == '\t' || c == '\n') |>.filter (·.trim ≠ "")
  toks.foldl (init := []) fun acc tok =>
    match tok.splitOn ":" with
    | nm :: ty0 :: _ =>
        let ty1 := (ty0.splitOn "|").getD 0 ty0
        let ty := dropRightWhile ty1.trim (fun c => !(c.isAlphanum || c == '_'))
        acc ++ [(nm.trim, ty)]
    | _ => acc

def sigInputs (sig : String) : List (String × String) :=
  match sig.splitOn "->" with
  | lhs :: _ =>
      if lhs.contains '∅' then [] else parseSigSideTypes lhs
  | _ => []

def sigHasContOutput (sig : String) : Bool :=
  match sig.splitOn "->" with
  | _lhs :: rhs :: _ => (rhs.splitOn ":Continuation").length > 1
  | _ => false

structure InitArg where
  fift : String
  lean : Value

instance : Inhabited InitArg where
  default := { fift := "0", lean := .int (.num 0) }

def emptySlice : Slice := Slice.ofCell Cell.empty

def emptyBuilder : Builder := Builder.empty

def cell1 : Cell :=
  Cell.mkOrdinary #[true] #[]

def slice1 : Slice :=
  Slice.ofCell cell1

def builder1 : Builder :=
  Builder.empty.storeBits #[true]

def tuple1 : Array Value :=
  #[.int (.num 1)]

def mkInitArgVariants (nm ty : String) : Option (Array InitArg) :=
  match ty with
  | "Int" =>
      let base : Int :=
        if nm == "p" || nm == "r" || nm == "n" then
          0
        else
          1
      let vals : List Int := ([base, 0, 1, -1, 2, -2, 127, -128]).eraseDups
      some <| vals.toArray.map (fun n => { fift := toString n, lean := .int (.num n) })
  | "Bool" =>
      some #[
        { fift := "0", lean := .int (.num 0) },
        { fift := "1", lean := .int (.num 1) }
      ]
  | "Any" =>
      some #[
        { fift := "1", lean := .int (.num 1) },
        { fift := "N", lean := .null }
      ]
  | "Cell" =>
      some #[
        { fift := "C", lean := .cell Cell.empty },
        { fift := "C1", lean := .cell cell1 }
      ]
  | "Slice" =>
      some #[
        { fift := "S", lean := .slice emptySlice },
        { fift := "S1", lean := .slice slice1 }
      ]
  | "Builder" =>
      some #[
        { fift := "B", lean := .builder emptyBuilder },
        { fift := "B1", lean := .builder builder1 }
      ]
  | "Tuple" =>
      some #[
        { fift := "T", lean := .tuple #[] },
        { fift := "T1", lean := .tuple tuple1 }
      ]
  | "Continuation" =>
      some #[
        { fift := "K", lean := .cont (.quit 0) },
        { fift := "K1", lean := .cont (.quit 1) }
      ]
  | _ =>
      none

def buildCodeCell (row : InstrRow) : Except String Cell := do
  if row.checkLen = 0 || row.skipLen = 0 || row.checkLen > row.skipLen || row.skipLen > 1023 then
    throw s!"invalid layout for {row.name}: checkLen={row.checkLen} skipLen={row.skipLen}"
  let probe := mkProbeCell row.pfx row.checkLen row.skipLen
  match decodeCp0WithBits (Slice.ofCell probe) with
  | .error e => throw s!"decodeCp0WithBits failed for {row.name}: {reprStr e}"
  | .ok (_instr, _totBits, rest) =>
      let usedBits := rest.bitPos
      let usedRefs := rest.refPos
      let bits := probe.bits.take usedBits
      let refs := probe.refs.take usedRefs
      pure <| Cell.mkOrdinary bits refs

def cellAppend (a b : Cell) : Except String Cell := do
  if a.bits.size + b.bits.size > 1023 then
    throw "code too large to concatenate (bits)"
  if a.refs.size + b.refs.size > 4 then
    throw "code too large to concatenate (refs)"
  pure <| Cell.mkOrdinary (a.bits ++ b.bits) (a.refs ++ b.refs)

def execInstrCell : Cell :=
  Cell.mkOrdinary (natToBits 0xd8 8) #[]

structure OracleOut where
  exitRaw : Int
  gasUsed : Int
  stackTop : Array String
  deriving Repr

def parseOracle (stdout : String) : IO OracleOut := do
  let lines := stdout.splitOn "\n" |>.map (·.trim) |>.filter (· ≠ "")
  let mut exitRaw? : Option Int := none
  let mut gasUsed? : Option Int := none
  let mut depth? : Option Nat := none
  let mut stackTop : Array String := #[]
  for ln in lines do
    let cols := ln.splitOn "\t"
    match cols with
    | ["EXIT", x] =>
        match x.toInt? with
        | some n => exitRaw? := some n
        | none => die s!"oracle: bad EXIT '{x}'"
    | ["GAS", x] =>
        match x.toInt? with
        | some n => gasUsed? := some n
        | none => die s!"oracle: bad GAS '{x}'"
    | ["DEPTH", x] =>
        match x.toNat? with
        | some n => depth? := some n
        | none => die s!"oracle: bad DEPTH '{x}'"
    | ["STACK", idx, v] =>
        match idx.toNat? with
        | some i =>
            if i != stackTop.size then
              die s!"oracle: unexpected STACK idx={i} (expected {stackTop.size})"
            stackTop := stackTop.push v
        | none => die s!"oracle: bad STACK idx '{idx}'"
    | _ =>
        pure ()
  let exitRaw ←
    match exitRaw? with
    | some x => pure x
    | none => die "oracle: missing EXIT"
  let gasUsed ←
    match gasUsed? with
    | some x => pure x
    | none => die "oracle: missing GAS"
  let depth ←
    match depth? with
    | some x => pure x
    | none => die "oracle: missing DEPTH"
  if stackTop.size != depth then
    die s!"oracle: STACK count mismatch (DEPTH={depth}, STACK={stackTop.size})"
  pure { exitRaw, gasUsed, stackTop }

def runOracle (code : Cell) (stackArgs : List String) : IO OracleOut := do
  let tonFift := (← IO.getEnv "TON_FIFT_BIN").getD "/Users/daniil/Coding/ton/build/crypto/fift"
  let tonLib := (← IO.getEnv "TON_FIFT_LIB").getD "/Users/daniil/Coding/ton/crypto/fift/lib"
  let oracleScript := (← IO.getEnv "TVMLEANTON_ORACLE_FIF").getD "tools/ton_oracle_runvm.fif"
  let bocBytes ←
    match stdBocSerialize code with
    | .ok b => pure b
    | .error e => die s!"stdBocSerialize failed: {reprStr e}"
  let codeHex := bytesToHex bocBytes
  let args :=
    #[
      s!"-I{tonLib}",
      "-s",
      oracleScript,
      codeHex
    ] ++ stackArgs.toArray
  let res ← IO.Process.output { cmd := tonFift, args := args, env := #[("GLOG_minloglevel", "2")] }
  if res.exitCode != 0 then
    die s!"oracle process failed (exit={res.exitCode}):\n{res.stderr}\n{res.stdout}"
  parseOracle res.stdout

def runLean (code : Cell) (initStack : Array Value) (fuel : Nat := 2_000_000) : StepResult :=
  -- Use an iterative runner (not `VmState.run` recursion) so we can allow enough steps for
  -- structured-loop opcodes to reach out-of-gas deterministically.
  Id.run do
    let mut stCur : VmState := { VmState.initial code with stack := initStack }
    let mut fuelCur : Nat := fuel
    let mut res : StepResult := .continue stCur

    while fuelCur > 0 do
      match stCur.step with
      | .continue st' =>
          stCur := st'
          res := .continue st'
          fuelCur := fuelCur - 1
      | .halt exitCode st' =>
          res := .halt exitCode st'
          stCur := st'
          fuelCur := 0

    match res with
    | .continue st' =>
        .halt (Excno.fatal.toInt) st'
    | .halt exitCode st' =>
        -- Mirror the C++ commit wrapper shape; precise commit checks come later.
        if exitCode = -1 ∨ exitCode = -2 then
          let (ok, st'') := st'.tryCommit
          if ok then
            .halt exitCode st''
          else
            let stFail := { st'' with stack := #[.int (.num 0)] }
            .halt (~~~ Excno.cellOv.toInt) stFail
        else
          .halt exitCode st'

def buildVariants (inputs : List (String × String)) : IO (Array (Array InitArg)) := do
  let mut varsPerArg : Array (Array InitArg) := #[]
  for (nm, ty) in inputs do
    match mkInitArgVariants nm ty with
    | some vs => varsPerArg := varsPerArg.push vs
    | none =>
        die s!"unsupported input type: {nm}:{ty}"

  let base : Array InitArg :=
    Array.ofFn (n := varsPerArg.size) fun i =>
      let vs := varsPerArg[i.1]!
      vs[0]!
  let mut out : Array (Array InitArg) := #[base]
  for i in [0:varsPerArg.size] do
    let vs := varsPerArg[i]!
    if vs.size > 1 then
      for j in [1:vs.size] do
        out := out.push (base.set! i vs[j]!)
  pure out

def validateRow (row : InstrRow) (maxVariantsPerInstr : Nat) (verbose : Bool := false) : IO Unit := do
  let inputs := sigInputs row.signature
  let variantsAll ← buildVariants inputs
  let code0 ←
    match buildCodeCell row with
    | .ok c => pure c
    | .error e => die e
  let code ←
    if sigHasContOutput row.signature then
      match cellAppend code0 execInstrCell with
      | .ok c => pure c
      | .error e => die s!"{row.name}: {e}"
    else
      pure code0
  let variants := variantsAll.take (Nat.max 1 maxVariantsPerInstr)
  for vidx in [0:variants.size] do
    let init := variants[vidx]!
    if verbose then
      let argDump := String.intercalate " " (init.toList.map (·.fift))
      IO.println s!"{row.name} (variant {vidx+1}/{variants.size}): {argDump}"
    let initStack : Array Value := init.map (·.lean)
    let initArgs : List String := init.toList.map (·.fift)
    let oracle ← runOracle code initArgs
    let leanRes := runLean code initStack
    let (leanExit, stF) ←
      match leanRes with
      | .halt ec st => pure (ec, st)
      | .continue _ => die s!"{row.name}: Lean did not halt (fuel exhausted)"
    let exitRawLean : Int := ~~~ leanExit
    let gasUsedLean : Int := stF.gas.gasConsumed
    if exitRawLean != oracle.exitRaw then
      die s!"{row.name} (variant {vidx+1}): EXIT mismatch lean_raw={exitRawLean} oracle={oracle.exitRaw} (lean_exit={leanExit})"
    if gasUsedLean != oracle.gasUsed then
      die s!"{row.name} (variant {vidx+1}): GAS mismatch lean={gasUsedLean} oracle={oracle.gasUsed}"
    let stackLeanTop : Array String :=
      Array.ofFn (n := stF.stack.size) fun i =>
        canonValue (stF.stack[stF.stack.size - 1 - i.1]!)
    if stackLeanTop.size != oracle.stackTop.size then
      die s!"{row.name} (variant {vidx+1}): DEPTH mismatch lean={stackLeanTop.size} oracle={oracle.stackTop.size}"
    for i in [0:stackLeanTop.size] do
      let a := stackLeanTop[i]!
      let b := oracle.stackTop[i]!
      if a != b then
        die s!"{row.name} (variant {vidx+1}): STACK mismatch at idx={i} lean='{a}' oracle='{b}'"

def main (args : List String) : IO UInt32 := do
  let limit? : Option Nat :=
    match args.dropWhile (· != "--limit") with
    | _ :: n :: _ => n.toNat?
    | _ => none
  let onlyName? : Option String :=
    match args.dropWhile (· != "--only") with
    | _ :: n :: _ => some n
    | _ => none
  let variantsPerInstr : Nat :=
    match args.dropWhile (· != "--variants") with
    | _ :: n :: _ => n.toNat?.getD 1
    | _ => 1
  let verbose : Bool := args.any (· == "--verbose")

  let path := System.mkFilePath ["docs", "progress", "tvm_spec_index.json"]
  let txt ← IO.FS.readFile path
  let idx ←
    match Lean.Json.parse txt with
    | .ok j => pure j
    | .error e => die s!"failed to parse {path}: {e}"

  let rows ← parseRows idx
  let rows :=
    match onlyName? with
    | some n => rows.filter (fun (r : InstrRow) => r.name == n)
    | none => rows
  let rows :=
    match limit? with
    | some k => rows.take k
    | none => rows

  for r in rows do
    validateRow r variantsPerInstr verbose

  IO.println "ok"
  return 0

end TvmLeanOracleValidate

def main (args : List String) : IO UInt32 :=
  TvmLeanOracleValidate.main args
