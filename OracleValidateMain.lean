import Lean
import TvmLean

open TvmLean

namespace TvmLeanOracleValidate

def die (msg : String) : IO α :=
  throw <| IO.userError msg

def base64Val (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then
    some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'z' then
    some (26 + (c.toNat - 'a'.toNat))
  else if '0' ≤ c ∧ c ≤ '9' then
    some (52 + (c.toNat - '0'.toNat))
  else if c = '+' then
    some 62
  else if c = '/' then
    some 63
  else
    none

def base64Decode (input : String) : Except String ByteArray := do
  let chars := (input.trim.data.filter (fun c => !c.isWhitespace)).toArray
  if chars.size % 4 ≠ 0 then
    throw s!"base64 length must be a multiple of 4, got {chars.size}"

  let groups := chars.size / 4
  let mut out : Array UInt8 := #[]

  for gi in [0:groups] do
    let i := gi * 4
    let c0 := chars[i]!
    let c1 := chars[i + 1]!
    let c2 := chars[i + 2]!
    let c3 := chars[i + 3]!

    let v0 ←
      match base64Val c0 with
      | some v => pure v
      | none => throw s!"invalid base64 char '{c0}'"
    let v1 ←
      match base64Val c1 with
      | some v => pure v
      | none => throw s!"invalid base64 char '{c1}'"

    let pad2 := c2 = '='
    let pad3 := c3 = '='
    if pad2 && !pad3 then
      throw "invalid base64 padding"
    if (pad2 || pad3) && gi ≠ groups - 1 then
      throw "invalid base64 padding (must be in the last block)"

    let v2 ←
      if pad2 then
        pure 0
      else
        match base64Val c2 with
        | some v => pure v
        | none => throw s!"invalid base64 char '{c2}'"
    let v3 ←
      if pad3 then
        pure 0
      else
        match base64Val c3 with
        | some v => pure v
        | none => throw s!"invalid base64 char '{c3}'"

    let b0 : Nat := (v0 <<< 2) ||| (v1 >>> 4)
    out := out.push (UInt8.ofNat b0)
    if !pad2 then
      let b1 : Nat := ((v1 &&& 0x0f) <<< 4) ||| (v2 >>> 2)
      out := out.push (UInt8.ofNat b1)
    if !pad3 then
      let b2 : Nat := ((v2 &&& 0x03) <<< 6) ||| v3
      out := out.push (UInt8.ofNat b2)

  return ByteArray.mk out

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

def decodeCellBoc (s : String) : Except String Cell := do
  let bytes ← base64Decode s
  match stdBocDeserialize bytes with
  | .ok c => pure c
  | .error e => throw s!"stdBocDeserialize failed: {e}"

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

def mkProbeCell (pfxBits : Nat) (checkLen : Nat) (argsVal : Nat) (argsLen : Nat) (tail : BitString := #[])
    (refs : Array Cell := Array.replicate 4 Cell.empty) : Cell :=
  let bitsLen : Nat := checkLen + argsLen + tail.size
  let padLen : Nat := Nat.min 512 (1023 - bitsLen)
  let pad : BitString := Array.replicate padLen false
  let bits : BitString := natToBits pfxBits checkLen ++ natToBits argsVal argsLen ++ tail ++ pad
  let refs' : Array Cell :=
    if refs.size < 4 then
      refs ++ Array.replicate (4 - refs.size) Cell.empty
    else
      refs.take 4
  Cell.mkOrdinary bits refs'

structure InstrRow where
  name : String
  signature : String
  layoutKind : String
  pfx : Nat
  args : Array Lean.Json
  checkLen : Nat
  skipLen : Nat

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
    let layoutKind ←
      match findKey? "kind" layoutObj with
      | some j => asStr j
      | none => die s!"missing layout.kind for {name}"
    let pfx ←
      match findKey? "prefix" layoutObj with
      | some j => asNat j
      | none => pure 0
    let args ←
      match findKey? "args" layoutObj with
      | some j => asArr j
      | none => pure #[]
    let checkLen ←
      match findKey? "checkLen" layoutObj with
      | some j => asNat j
      | none => pure 0
    let skipLen ←
      match findKey? "skipLen" layoutObj with
      | some j => asNat j
      | none => pure 0
    out := out.push { name, signature, layoutKind, pfx, args, checkLen, skipLen }
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

def cell2 : Cell :=
  -- 4 bits: 1010
  Cell.mkOrdinary #[true, false, true, false] #[]

def slice1 : Slice :=
  Slice.ofCell cell1

def slice2 : Slice :=
  Slice.ofCell cell2

def builder1 : Builder :=
  Builder.empty.storeBits #[true]

def builder2 : Builder :=
  Builder.empty.storeBits #[true, false, true, false]

def tuple1 : Array Value :=
  #[.int (.num 1)]

def tuple2 : Array Value :=
  #[.int (.num 1), .int (.num 2)]

def mkIntArg (n : Int) : InitArg :=
  { fift := toString n, lean := .int (.num n) }

def mkIntStackAsc (depth : Nat) : Array InitArg :=
  Array.ofFn (n := depth) fun i =>
    mkIntArg (Int.ofNat (i.1 + 1))

def mkIntStackDesc (depth : Nat) : Array InitArg :=
  Array.ofFn (n := depth) fun i =>
    mkIntArg (Int.ofNat (depth - i.1))

def mkStackMixed (depth : Nat) : Array InitArg :=
  let base := mkIntStackAsc depth
  let base :=
    if depth > 0 then
      base.set! (depth - 1) { fift := "C1", lean := .cell cell1 }
    else
      base
  let base :=
    if depth > 1 then
      base.set! (depth - 2) { fift := "S1", lean := .slice slice1 }
    else
      base
  let base :=
    if depth > 2 then
      base.set! (depth - 3) { fift := "B1", lean := .builder builder1 }
    else
      base
  let base :=
    if depth > 3 then
      base.set! (depth - 4) { fift := "T1", lean := .tuple tuple1 }
    else
      base
  base

def mkInitArgVariants (nm ty : String) : Option (Array InitArg) :=
  match ty with
  | "Int" =>
      let base : Int := if nm == "p" || nm == "r" || nm == "n" then 0 else 1
      let i31 : Int := (Int.ofNat (1 <<< 31))
      let i63 : Int := (Int.ofNat (1 <<< 63))
      let i255 : Int := (Int.ofNat (1 <<< 255))
      let minInt257 : Int := -(Int.ofNat (1 <<< 256))
      let maxInt257 : Int := (Int.ofNat (1 <<< 256)) - 1
      let vals : List Int :=
        ([
          base,
          0,
          1,
          -1,
          2,
          -2,
          3,
          -3,
          7,
          -7,
          8,
          -8,
          127,
          -128,
          255,
          -256,
          i31 - 1,
          -i31,
          i63 - 1,
          -i63,
          i255 - 1,
          -i255,
          maxInt257,
          minInt257
        ]).eraseDups
      let nums : Array InitArg :=
        vals.toArray.map (fun n => { fift := toString n, lean := .int (.num n) })
      some nums
  | "Bool" =>
      some #[
        { fift := "0", lean := .int (.num 0) },
        { fift := "1", lean := .int (.num 1) },
        { fift := "-1", lean := .int (.num (-1)) },
        { fift := "2", lean := .int (.num 2) }
      ]
  | "Any" =>
      some #[
        { fift := "1", lean := .int (.num 1) },
        { fift := "N", lean := .null },
        { fift := "C1", lean := .cell cell1 },
        { fift := "S1", lean := .slice slice1 },
        { fift := "B1", lean := .builder builder1 },
        { fift := "T1", lean := .tuple tuple1 },
        { fift := "K1", lean := .cont (.quit 1) }
      ]
  | "Cell" =>
      some #[
        { fift := "C", lean := .cell Cell.empty },
        { fift := "C1", lean := .cell cell1 },
        { fift := "C2", lean := .cell cell2 }
      ]
  | "Slice" =>
      some #[
        { fift := "S", lean := .slice emptySlice },
        { fift := "S1", lean := .slice slice1 },
        { fift := "S2", lean := .slice slice2 }
      ]
  | "Builder" =>
      some #[
        { fift := "B", lean := .builder emptyBuilder },
        { fift := "B1", lean := .builder builder1 },
        { fift := "B2", lean := .builder builder2 }
      ]
  | "Tuple" =>
      some #[
        { fift := "T", lean := .tuple #[] },
        { fift := "T1", lean := .tuple tuple1 },
        { fift := "T2", lean := .tuple tuple2 }
      ]
  | "Continuation" =>
      some #[
        { fift := "K", lean := .cont (.quit 0) },
        { fift := "K1", lean := .cont (.quit 1) },
        { fift := "K2", lean := .cont (.quit 2) }
      ]
  | _ =>
      none

structure ImmField where
  tag : String
  name : String
  len : Nat
  range? : Option (Int × Int)
  deriving Repr, Inhabited

def asInt (j : Lean.Json) : Except String Int :=
  match j with
  | .num n =>
      if n.exponent != 0 then
        throw s!"expected Int JSON number, got {n}"
      else
        pure n.mantissa
  | _ => throw "expected JSON number"

def parseRange? (j : Lean.Json) : Except String (Option (Int × Int)) := do
  match j with
  | .obj o =>
      let xs := o.toList
      let minJ ←
        match findKey? "min" xs with
        | some v => pure v
        | none => throw "range missing min"
      let maxJ ←
        match findKey? "max" xs with
        | some v => pure v
        | none => throw "range missing max"
      let minS ←
        match minJ with
        | .str s => pure s
        | _ => throw "range.min must be a string"
      let maxS ←
        match maxJ with
        | .str s => pure s
        | _ => throw "range.max must be a string"
      let minI ←
        match minS.toInt? with
        | some i => pure i
        | none => throw s!"range.min not an Int: {minS}"
      let maxI ←
        match maxS.toInt? with
        | some i => pure i
        | none => throw s!"range.max not an Int: {maxS}"
      pure (some (minI, maxI))
  | _ =>
      pure none

partial def parseImmFields (row : InstrRow) : Except String (Array ImmField) := do
  let argsLen : Nat := row.skipLen - row.checkLen
  let rec parseOne (j : Lean.Json) : Except String (Array ImmField) := do
    match j with
    | .obj o =>
        let xs := o.toList
        let tag ←
          match findKey? "$" xs with
          | some (.str s) => pure s
          | _ => throw "layout arg missing $ tag"
        if tag == "delta" then
          let inner ←
            match findKey? "arg" xs with
            | some v => pure v
            | none => throw "delta arg missing .arg"
          parseOne inner
        else if tag == "minusOne" || tag == "s1" then
          pure #[]
        else if tag == "dict" || tag == "refCodeSlice" || tag == "codeSlice" || tag == "inlineCodeSlice" ||
            tag == "largeInt" || tag == "slice" || tag == "debugstr" then
          pure #[]
        else
          let name :=
            match findKey? "name" xs with
            | some (.str s) => s
            | _ => tag
          let len : Nat :=
            match findKey? "len" xs with
            | some (.num n) => (if n.exponent == 0 && n.mantissa >= 0 then n.mantissa.toNat else 0)
            | _ => 0
          let range? ←
            match findKey? "range" xs with
            | some r => parseRange? r
            | none => pure none
          pure #[{ tag, name, len, range? }]
    | _ =>
        throw "layout arg must be an object"

  let mut fields : Array ImmField := #[]
  for a in row.args do
    let fs ← parseOne a
    fields := fields ++ fs

  let knownBits : Nat := fields.foldl (init := 0) fun acc f => acc + f.len
  let mut unknownIdxs2 : Array Nat := #[]
  for i in [0:fields.size] do
    if fields[i]!.len == 0 then
      unknownIdxs2 := unknownIdxs2.push i

  if argsLen < knownBits then
    throw s!"{row.name}: layout args bits exceed skipLen-checkLen ({knownBits} > {argsLen})"

  if unknownIdxs2.size == 1 then
    let rem := argsLen - knownBits
    let idx := unknownIdxs2[0]!
    fields := fields.set! idx { fields[idx]! with len := rem }
  else if unknownIdxs2.size == 0 then
    if knownBits == 0 && argsLen > 0 then
      fields := #[{ tag := "raw", name := "args", len := argsLen, range? := none }]
    else if knownBits != argsLen then
      let rem := argsLen - knownBits
      fields := fields.push { tag := "raw", name := "args", len := rem, range? := none }
  else
    throw s!"{row.name}: cannot infer lengths for {unknownIdxs2.size} layout args (argsLen={argsLen}, knownBits={knownBits})"

  pure fields

def repValsSigned (minI maxI : Int) : Array Int :=
  let cands : List Int := [minI, minI + 1, -1, 0, 1, maxI - 1, maxI]
  (cands.filter (fun x => minI ≤ x ∧ x ≤ maxI)).eraseDups.toArray

def repValsUnsigned (minI maxI : Int) : Array Int :=
  let cands : List Int := [minI, minI + 1, 0, 1, maxI - 1, maxI]
  (cands.filter (fun x => minI ≤ x ∧ x ≤ maxI)).eraseDups.toArray

def encodeImmField (f : ImmField) (x : Int) : Except String Nat := do
  if f.len = 0 then
    throw s!"encodeImmField: zero-len field {reprStr f}"
  let m : Nat := 1 <<< f.len
  let mask : Nat := m - 1
  if f.tag == "int" then
    if x >= 0 then
      pure (x.toNat &&& mask)
    else
      let y : Int := x + Int.ofNat m
      if y < 0 then
        throw s!"encodeImmField: int out of range for {f.name}: {x}"
      pure (y.toNat &&& mask)
  else if f.tag == "tinyInt" then
    -- Only used for PUSHINT_4 (range -5..10). Encoding is 4-bit two's complement with a restricted range.
    if x >= 0 then
      pure (x.toNat &&& mask)
    else
      let y : Int := x + Int.ofNat m
      if y < 0 then
        throw s!"encodeImmField: tinyInt out of range for {f.name}: {x}"
      pure (y.toNat &&& mask)
  else
    if x < 0 then
      throw s!"encodeImmField: negative value for unsigned field {f.name}: {x}"
    pure (x.toNat &&& mask)

def packArgsVal (fields : Array ImmField) (vals : Array Int) : Except String Nat := do
  if fields.size != vals.size then
    throw "packArgsVal: arity mismatch"
  let mut acc : Nat := 0
  for i in [0:fields.size] do
    let f := fields[i]!
    let v := vals[i]!
    let enc ← encodeImmField f v
    acc := (acc <<< f.len) ||| enc
  pure acc

def buildArgsValVariants (row : InstrRow) (maxCodeVariants : Nat) : Except String (Array Nat) := do
  let argsLen : Nat := row.skipLen - row.checkLen
  if argsLen = 0 then
    return #[0]

  let fields ← parseImmFields row

  let baseVals : Array Int :=
    Array.ofFn (n := fields.size) fun i =>
      match fields[i.1]!.range? with
      | some (minI, maxI) =>
          if minI ≤ 0 ∧ 0 ≤ maxI then 0 else minI
      | none =>
          0

  let mut out : Array Nat := #[]

  let baseArgs ← packArgsVal fields baseVals
  if !(out.contains baseArgs) then
    out := out.push baseArgs

  for i in [0:fields.size] do
    if out.size >= maxCodeVariants then
      break
    let f := fields[i]!
    let alts : Array Int :=
      match f.range? with
      | some (minI, maxI) =>
          if f.tag == "int" || f.tag == "tinyInt" then
            repValsSigned minI maxI
          else
            repValsUnsigned minI maxI
      | none =>
          let maxU : Int := Int.ofNat ((1 <<< f.len) - 1)
          repValsUnsigned 0 maxU
    for v in alts do
      if out.size >= maxCodeVariants then
        break
      if v == baseVals[i]! then
        continue
      let vals' := baseVals.set! i v
      let av ← packArgsVal fields vals'
      if !(out.contains av) then
        out := out.push av

  pure out

def buildCodeCellWithArgsVal (row : InstrRow) (argsVal : Nat) (tail : BitString := #[])
    (refs : Array Cell := Array.replicate 4 Cell.empty) : Except String Cell := do
  if row.checkLen = 0 || row.skipLen = 0 || row.checkLen > row.skipLen || row.skipLen > 1023 then
    throw s!"invalid layout for {row.name}: checkLen={row.checkLen} skipLen={row.skipLen}"
  let argsLen : Nat := row.skipLen - row.checkLen
  let pfxBits : Nat :=
    if row.layoutKind == "fixed-range" || row.layoutKind == "ext-range" then
      row.pfx >>> argsLen
    else
      row.pfx
  let probe := mkProbeCell pfxBits row.checkLen (argsVal &&& ((1 <<< argsLen) - 1)) argsLen tail refs
  match decodeCp0WithBits (Slice.ofCell probe) with
  | .error e => throw s!"decodeCp0WithBits failed for {row.name}: {reprStr e}"
  | .ok (_instr, _totBits, rest) =>
      let usedBits := rest.bitPos
      let usedRefs := rest.refPos
      let bits := probe.bits.take usedBits
      let refs := probe.refs.take usedRefs
      pure <| Cell.mkOrdinary bits refs

def buildCodeCells (row : InstrRow) (maxCodeVariants : Nat) : Except String (Array (Nat × Cell)) := do
  let maxCodeVariants := Nat.max 1 maxCodeVariants
  let argsVals ← buildArgsValVariants row maxCodeVariants
  let mut out : Array (Nat × Cell) := #[]
  for av in argsVals do
    match buildCodeCellWithArgsVal row av with
    | .ok c => out := out.push (av, c)
    | .error _ => pure ()
  if out.isEmpty then
    throw s!"{row.name}: failed to build any code variants"
  pure out

def buildCodeCell (row : InstrRow) : Except String Cell := do
  let argsLen : Nat := row.skipLen - row.checkLen
  let argsVal0 : Nat :=
    if row.layoutKind == "fixed-range" || row.layoutKind == "ext-range" then
      row.pfx &&& ((1 <<< argsLen) - 1)
    else
      0
  buildCodeCellWithArgsVal row argsVal0

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
  c4Hash : String
  c5Hash : String
  stackTop : Array String
  deriving Repr

def parseOracle (stdout : String) : IO OracleOut := do
  let lines := stdout.splitOn "\n" |>.map (·.trim) |>.filter (· ≠ "")
  let mut exitRaw? : Option Int := none
  let mut gasUsed? : Option Int := none
  let mut c4Hash? : Option String := none
  let mut c5Hash? : Option String := none
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
    | ["C4", x] =>
        c4Hash? := some x
    | ["C5", x] =>
        c5Hash? := some x
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
  let c4Hash ←
    match c4Hash? with
    | some x => pure x
    | none => die "oracle: missing C4"
  let c5Hash ←
    match c5Hash? with
    | some x => pure x
    | none => die "oracle: missing C5"
  if stackTop.size != depth then
    die s!"oracle: STACK count mismatch (DEPTH={depth}, STACK={stackTop.size})"
  pure { exitRaw, gasUsed, c4Hash, c5Hash, stackTop }

def fiftQuote (s : String) : String :=
  let s := s.replace "\\" "\\\\"
  let s := s.replace "\"" "\\\""
  "\"" ++ s ++ "\""

def parseOracleBatch (stdout : String) (nCases : Nat) : IO (Array OracleOut) := do
  let lines := stdout.splitOn "\n" |>.map (·.trim) |>.filter (· ≠ "")
  let mut cur? : Option Nat := none
  let mut buf : Array String := #[]
  let mut outs : Array (Option OracleOut) := Array.replicate nCases none
  for ln in lines do
    let cols := ln.splitOn "\t"
    match cols with
    | ["CASE", x] =>
        if cur?.isSome then
          die s!"oracle batch: nested CASE (prev={cur?}, new='{x}')"
        match x.toNat? with
        | some i =>
            if i >= nCases then
              die s!"oracle batch: CASE id out of range: {i} (n={nCases})"
            cur? := some i
            buf := #[]
        | none =>
            die s!"oracle batch: bad CASE id '{x}'"
    | ["ENDCASE", x] =>
        match (cur?, x.toNat?) with
        | (some i, some j) =>
            if i != j then
              die s!"oracle batch: ENDCASE mismatch start={i} end={j}"
            let out ← parseOracle (String.intercalate "\n" buf.toList)
            if outs[i]!.isSome then
              die s!"oracle batch: duplicate output for case {i}"
            outs := outs.set! i (some out)
            cur? := none
            buf := #[]
        | (none, _) =>
            die s!"oracle batch: ENDCASE without CASE ({x})"
        | (_, none) =>
            die s!"oracle batch: bad ENDCASE id '{x}'"
    | _ =>
        if cur?.isSome then
          buf := buf.push ln
        else
          pure ()

  if cur?.isSome then
    die s!"oracle batch: unterminated CASE {cur?}"

  let mut outFinal : Array OracleOut := #[]
  for i in [0:nCases] do
    match outs[i]! with
    | some o => outFinal := outFinal.push o
    | none => die s!"oracle batch: missing output for case {i}"
  pure outFinal

def runOracleBatch (cases : Array (Cell × List String)) : IO (Array OracleOut) := do
  if cases.isEmpty then
    return #[]
  let tonFift := (← IO.getEnv "TON_FIFT_BIN").getD "/Users/daniil/Coding/ton/build/crypto/fift"
  let tonLib := (← IO.getEnv "TON_FIFT_LIB").getD "/Users/daniil/Coding/ton/crypto/fift/lib"
  let oracleLib := (← IO.getEnv "TVMLEANTON_ORACLE_LIB_FIF").getD "tools/ton_oracle_runvm_lib.fif"
  let tmpDir := (← IO.getEnv "TVMLEANTON_ORACLE_TMP").getD "/tmp"
  let keepTmp : Bool := (← IO.getEnv "TVMLEANTON_ORACLE_KEEP_TMP").getD "0" == "1"

  let mut script := s!"{fiftQuote oracleLib} include\n\n"
  for idx in [0:cases.size] do
    let (code, stackArgs) := cases[idx]!
    let bocBytes ←
      match stdBocSerialize code with
      | .ok b => pure b
      | .error e => die s!"stdBocSerialize failed: {reprStr e}"
    let codeHex := bytesToHex bocBytes
    let idStr := toString idx
    script := script ++ s!"\"CASE\" type 9 emit {fiftQuote idStr} type cr\n"
    for tok in stackArgs do
      script := script ++ s!"{fiftQuote tok} push-token\n"
    script := script ++ s!"{fiftQuote codeHex} oracle-run\n"
    script := script ++ s!"\"ENDCASE\" type 9 emit {fiftQuote idStr} type cr\n\n"
  script := script ++ "bye\n"

  let pid ← IO.Process.getPID
  let now ← IO.monoNanosNow
  let tmpPath := System.mkFilePath [tmpDir, s!"tvmlean_oracle_batch_{pid}_{now}.fif"]
  IO.FS.writeFile tmpPath script
  try
    let args := #[
      s!"-I{tonLib}",
      "-s",
      toString tmpPath
    ]
    let res ← IO.Process.output { cmd := tonFift, args := args, env := #[("GLOG_minloglevel", "2")] }
    if res.exitCode != 0 then
      die s!"oracle batch process failed (exit={res.exitCode}):\n{res.stderr}\n{res.stdout}"
    parseOracleBatch res.stdout cases.size
  finally
    if !keepTmp then
      try
        IO.FS.removeFile tmpPath
      catch _ =>
        pure ()

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
    -- Standard deterministic c7 context (must match `tools/ton_oracle_runvm.fif`).
    let cfgGlobalIdBoc : String := "te6cckEBAQEABgAACP///xHmo3/3"
    let cfgMcGasPricesBoc : String :=
      "te6cckEBAQEATAAAlNEAAAAAAAAAZAAAAAAAD0JA3gAAAAAnEAAAAAAAAAAPQkAAAAAABCwdgAAAAAAAACcQAAAAAAAmJaAAAAAABfXhAAAAAAA7msoAKm2gQw=="
    let cfgGasPricesBoc : String :=
      "te6cckEBAQEATAAAlNEAAAAAAAAAZAAAAAAAAJxA3gAAAAABkAAAAAAAAAAPQkAAAAAAAA9CQAAAAAAAACcQAAAAAACYloAAAAAABfXhAAAAAAA7msoAGR7wcQ=="
    let cfgMcFwdPricesBoc : String :=
      "te6cckEBAQEAIwAAQuoAAAAAAJiWgAAAAAAnEAAAAAAAD0JAAAAAAYAAVVVVVX2jQy8="
    let cfgFwdPricesBoc : String :=
      "te6cckEBAQEAIwAAQuoAAAAAAAYagAAAAAABkAAAAAAAAJxAAAAAAYAAVVVVVXYlR3Q="
    let myAddrBoc : String :=
      "te6cckEBAQEAJAAAQ4AX+ASE+Zkibqtx1QAAadKu7Lvas3CH7AqhX7mcYqQbudAC/Bvd"

    let sliceOfBoc (boc : String) : Slice :=
      match (decodeCellBoc boc) with
      | .ok c => Slice.ofCell c
      | .error _ => Slice.ofCell Cell.empty

    let myAddr : Value := .slice (sliceOfBoc myAddrBoc)

    let unpacked : Array Value :=
      #[
        .null,
        .slice (sliceOfBoc cfgGlobalIdBoc),
        .slice (sliceOfBoc cfgMcGasPricesBoc),
        .slice (sliceOfBoc cfgGasPricesBoc),
        .slice (sliceOfBoc cfgMcFwdPricesBoc),
        .slice (sliceOfBoc cfgFwdPricesBoc),
        .null
      ]

    let balance : Value := .tuple #[.int (.num 50062889874), .null]
    let incomingValue : Value := .tuple #[.int (.num 13000000000), .null]
    let inMsgParams : Value :=
      .tuple #[
        .int (.num 0),
        .int (.num 0),
        myAddr,
        .int (.num 266669),
        .int (.num 66317877000004),
        .int (.num 1769644811),
        .int (.num 13000000000),
        .int (.num 13000000000),
        .null,
        .null
      ]

    let env : Array Value :=
      #[
        .int (.num 0x076ef1ea),
        .int (.num 0),
        .int (.num 0),
        .int (.num 1769644811),
        .int (.num 66317877000000),
        .int (.num 66317877000005),
        .int (.num 0),
        balance,
        myAddr,
        .null,
        .cell code,
        incomingValue,
        .int (.num 7),
        .null,
        .tuple unpacked,
        .int (.num 0),
        .null,
        inMsgParams
      ]

    let c7 : Array Value := #[.tuple env]

    let base : VmState := VmState.initial code 1_000_000 1_000_000
    let mut stCur : VmState :=
      { base with
        stack := initStack
        regs := { base.regs with c7 := c7 }
      }
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

def stackKey (st : Array InitArg) : String :=
  String.intercalate "|" (st.toList.map (·.fift))

def stackDedup (xs : Array (Array InitArg)) : Array (Array InitArg) :=
  Id.run do
    let mut out : Array (Array InitArg) := #[]
    for st in xs do
      let k := stackKey st
      if out.any (fun st' => stackKey st' == k) then
        continue
      out := out.push st
    out

def noisePrefixes : Array (Array InitArg) :=
  #[
    #[],
    #[mkIntArg 111],
    #[{ fift := "C1", lean := .cell cell1 }],
    #[mkIntArg 111, { fift := "C1", lean := .cell cell1 }],
    #[
      { fift := "S1", lean := .slice slice1 },
      { fift := "B1", lean := .builder builder1 },
      { fift := "T1", lean := .tuple tuple1 }
    ],
    #[mkIntArg 111, { fift := "S1", lean := .slice slice1 }, { fift := "C1", lean := .cell cell1 }]
  ]

def buildNoInputStacks (max : Nat) : Array (Array InitArg) :=
  let max := Nat.max 1 max
  let base : Array (Array InitArg) :=
    #[
      #[],
      #[mkIntArg 0],
      #[mkIntArg 1],
      #[mkIntArg (-1)],
      #[{ fift := "C1", lean := .cell cell1 }],
      #[{ fift := "S1", lean := .slice slice1 }],
      #[{ fift := "B1", lean := .builder builder1 }],
      #[{ fift := "T1", lean := .tuple tuple1 }],
      #[mkIntArg 1, mkIntArg 2],
      #[mkIntArg 1, { fift := "C1", lean := .cell cell1 }],
      #[
        { fift := "S1", lean := .slice slice1 },
        { fift := "B1", lean := .builder builder1 },
        { fift := "T1", lean := .tuple tuple1 }
      ],
      mkIntStackAsc 4,
      mkIntStackDesc 4,
      mkStackMixed 4,
      mkIntStackAsc 8,
      mkIntStackDesc 8,
      mkStackMixed 8,
      mkIntStackAsc 16,
      mkStackMixed 16,
      mkIntStackDesc 16
    ]
  (stackDedup base).take max

def wrongTypeFor (ty : String) : Option InitArg :=
  match ty with
  | "Int" => some { fift := "N", lean := .null }
  | "Bool" => some { fift := "C1", lean := .cell cell1 }
  | "Cell" => some { fift := "S1", lean := .slice slice1 }
  | "Slice" => some { fift := "C1", lean := .cell cell1 }
  | "Builder" => some { fift := "S1", lean := .slice slice1 }
  | "Tuple" => some (mkIntArg 1)
  | "Continuation" => some (mkIntArg 1)
  | "Any" => none
  | _ => none

def buildVariants (inputs : List (String × String)) (max : Nat) : IO (Array (Array InitArg)) := do
  let max := Nat.max 1 max
  if inputs.isEmpty then
    return buildNoInputStacks max

  let mut varsPerArg : Array (String × Array InitArg) := #[]
  for (nm, ty) in inputs do
    match mkInitArgVariants nm ty with
    | some vs => varsPerArg := varsPerArg.push (ty, vs)
    | none => die s!"unsupported input type: {nm}:{ty}"

  let baseArgs : Array InitArg :=
    Array.ofFn (n := varsPerArg.size) fun i =>
      let vs := varsPerArg[i.1]!.snd
      vs[0]!

  let mut core : Array (Array InitArg) := #[baseArgs]
  let maxAlt : Nat :=
    varsPerArg.foldl (init := 0) fun acc (_, vs) => Nat.max acc vs.size

  -- Balanced single-arg variations: for k=1.., vary each arg by k in round-robin.
  for k in [1:maxAlt] do
    for i in [0:varsPerArg.size] do
      let vs := varsPerArg[i]!.snd
      if vs.size > k then
        core := core.push (baseArgs.set! i vs[k]!)

  -- A few 2-arg combinations (useful for binary ops).
  if varsPerArg.size ≥ 2 then
    for k in [1:Nat.min 3 maxAlt] do
      for i in [0:varsPerArg.size] do
        for j in [i+1:varsPerArg.size] do
          let vsi := varsPerArg[i]!.snd
          let vsj := varsPerArg[j]!.snd
          if vsi.size > k && vsj.size > k then
            let st := (baseArgs.set! i vsi[k]!).set! j vsj[k]!
            core := core.push st

  core := stackDedup core

  let nArgs := varsPerArg.size
  let wantUnderflow : Nat := if nArgs > 0 then 2 else 0
  let wantWrong : Nat :=
    Nat.min 3 <| varsPerArg.foldl (init := 0) fun acc (ty, _vs) => acc + (if (wrongTypeFor ty).isSome then 1 else 0)
  let wantValid : Nat := Nat.max 1 (max - (wantUnderflow + wantWrong))

  let mut out : Array (Array InitArg) := #[]

  -- Valid cases, with deterministic "noise" prefixes to ensure deeper stack items are preserved.
  for idx in [0:core.size] do
    if out.size >= wantValid then
      break
    let pfx := noisePrefixes[idx % noisePrefixes.size]!
    out := out.push (pfx ++ core[idx]!)

  -- Wrong-type cases (one per arg, up to budget).
  for i in [0:varsPerArg.size] do
    if out.size >= wantValid + wantWrong then
      break
    let ty := varsPerArg[i]!.fst
    match wrongTypeFor ty with
    | some bad =>
        let st := baseArgs.set! i bad
        if !(out.any (fun st' => stackKey st' == stackKey st)) then
          out := out.push st
    | none => pure ()

  -- Underflow cases (empty + n-1).
  if nArgs > 0 && out.size < max then
    let st0 : Array InitArg := #[]
    if !(out.any (fun st' => stackKey st' == stackKey st0)) then
      out := out.push st0
  if nArgs > 1 && out.size < max then
    let st1 := baseArgs.take (nArgs - 1)
    if !(out.any (fun st' => stackKey st' == stackKey st1)) then
      out := out.push st1

  -- Fill any remaining slots with more valid cores (no extra noise) for breadth.
  for idx in [0:core.size] do
    if out.size >= max then
      break
    let st := core[idx]!
    if !(out.any (fun st' => stackKey st' == stackKey st)) then
      out := out.push st

  pure ((stackDedup out).take max)

def decodeFirstInstr (code : Cell) : Except String Instr := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (i, _n, _rest) => pure i
  | .error e => throw s!"decodeCp0WithBits failed: {reprStr e}"

def noSigNeedDepth (i : Instr) : Nat :=
  match i with
  | .push idx => idx + 1
  | .pop idx => idx + 1
  | .xchg0 idx => idx + 1
  | .xchg1 idx => idx + 1
  | .xchg x y => Nat.max x y + 1
  | .xchg2 x y => Nat.max x y + 1
  | .xchg3 x y z => Nat.max (Nat.max x y) z + 1
  | .xcpu x y => Nat.max x y + 1
  | .xc2pu x y z => Nat.max (Nat.max (Nat.max x y) z) 1 + 1
  | .xcpuxc x y z => Nat.max (Nat.max (Nat.max x y) 1 + 1) z
  | .xcpu2 x y z => Nat.max (Nat.max x y) z + 1
  | .puxc x y => Nat.max (x + 1) y
  | .puxc2 x y z => Nat.max (Nat.max (Nat.max (x + 1) 2) y) z
  | .puxcpu x y z => Nat.max (Nat.max (x + 1) y) z
  | .pu2xc x y _z => Nat.max (Nat.max (x + 1) y) 1
  | .push2 x y => Nat.max x y + 1
  | .push3 x y z => Nat.max (Nat.max x y) z + 1
  | .blkdrop n => Nat.max 1 n
  | .blkSwap x y => Nat.max 1 (x + y)
  | .reverse x y => Nat.max 1 (x + y)
  | .blkPush _x y => Nat.max 1 (y + 1)
  | .blkdrop2 x y => Nat.max 1 (x + y)
  | _ => 1

def validateRow (row : InstrRow) (maxStackVariantsPerInstr : Nat) (maxCodeVariantsPerInstr : Nat)
    (casesPerInstr? : Option Nat := none) (verbose : Bool := false) (maxNoSigDepth : Nat := 64) : IO Unit := do
  let codePairs0 ←
    match buildCodeCells row maxCodeVariantsPerInstr with
    | .ok cs => pure cs
    | .error e => die e
  let codePairs ←
    if sigHasContOutput row.signature then
      let mut out : Array (Nat × Cell) := #[]
      for (av, c) in codePairs0 do
        match cellAppend c execInstrCell with
        | .ok c' => out := out.push (av, c')
        | .error e => die s!"{row.name}: {e}"
      pure out
    else
      pure codePairs0

  if row.name == "RUNVM" then
    -- Minimal, deterministic RUNVM cases (mode=0), to avoid only testing stkUnd paths.
    let mkProg (bits : Array BitString) : IO (Cell × String) := do
      let allBits := bits.foldl (init := #[]) fun acc b => acc ++ b
      let cell := Cell.mkOrdinary allBits #[]
      let bocBytes ←
        match stdBocSerialize cell with
        | .ok b => pure b
        | .error e => die s!"RUNVM: stdBocSerialize failed: {reprStr e}"
      let hex := bytesToHex bocBytes
      pure (cell, hex)

    let retBits ←
      match encodeCp0 .ret with
      | .ok b => pure b
      | .error e => die s!"RUNVM: encodeCp0 RET failed: {reprStr e}"
    let push7Bits ←
      match encodeCp0 (.pushInt (.num 7)) with
      | .ok b => pure b
      | .error e => die s!"RUNVM: encodeCp0 PUSHINT 7 failed: {reprStr e}"

    let (progRetCell, progRetHex) ← mkProg #[retBits]
    let (progPush7RetCell, progPush7RetHex) ← mkProg #[push7Bits, retBits]

    let mkSliceArg (cell : Cell) (hex : String) : InitArg :=
      { fift := s!"SB:{hex}", lean := .slice (Slice.ofCell cell) }

    let progRet := mkSliceArg progRetCell progRetHex
    let progPush7Ret := mkSliceArg progPush7RetCell progPush7RetHex

    let casesWanted : Nat := (casesPerInstr?.getD 20) |> Nat.max 1

    let mkInitSimple (stackItems : Array InitArg) (prog : InitArg) : Array InitArg :=
      stackItems ++ #[mkIntArg (Int.ofNat stackItems.size), prog]

    let mkInitMode511 (stackItems : Array InitArg) (prog : InitArg) (retVals : Nat) : Array InitArg :=
      -- mode=511: hasRetVals + withData + loadC7 + returnGas + hasHardMax (+ sameC3 + push0)
      -- pop order (top->down): gasMax, gasLimit, c7, data, retVals, codeSlice, stackSize, stackItems...
      stackItems ++
        #[
          mkIntArg (Int.ofNat stackItems.size),
          prog,
          mkIntArg (Int.ofNat retVals),
          { fift := "C1", lean := .cell cell1 },
          { fift := "T1", lean := .tuple tuple1 },
          mkIntArg 1_000_000,
          mkIntArg 2_000_000
        ]

    let findCode? (mode : Nat) : Option Cell :=
      (codePairs.find? (fun (p : Nat × Cell) => p.fst == mode)).map (·.snd)

    let code0 := (findCode? 0).getD (codePairs[0]!.snd)
    let code1? := findCode? 1
    let code510? := findCode? 510
    let code511? := findCode? 511

    let mut cases : Array (Nat × Cell × Array InitArg) := #[]

    -- mode=0 "happy path" + a few deterministic errors
    cases := cases ++ #[
      (0, code0, mkInitSimple #[] progRet),
      (0, code0, mkInitSimple #[] progPush7Ret),
      (0, code0, mkInitSimple #[mkIntArg 5] progRet),
      (0, code0, mkInitSimple #[mkIntArg 5] progPush7Ret),
      (0, code0, mkInitSimple #[mkIntArg 1, mkIntArg 2] progPush7Ret),
      (0, code0, mkInitSimple #[mkIntArg 1, mkIntArg 2, mkIntArg 3] progRet),
      (0, code0, mkInitSimple #[{ fift := "C1", lean := .cell cell1 }] progRet),
      (0, code0, #[progRet]),                                   -- missing stackSize => stkUnd
      (0, code0, #[mkIntArg (-1), progRet]),                     -- negative stackSize => rangeChk
      (0, code0, #[mkIntArg 1, mkIntArg 2, progRet])             -- stackSize>available => rangeChk
    ]

    -- mode=1: sameC3 (no extra args), keep a smaller set
    match code1? with
    | some code1 =>
        cases := cases ++ #[
          (1, code1, mkInitSimple #[] progRet),
          (1, code1, mkInitSimple #[] progPush7Ret),
          (1, code1, mkInitSimple #[mkIntArg 7] progRet),
          (1, code1, #[progRet])                                  -- stkUnd still
        ]
    | none => pure ()

    -- mode=511: exercise full argument-pop order + retVals edge
    match code511? with
    | some code511 =>
        cases := cases ++ #[
          (511, code511, mkInitMode511 #[] progRet 1),
          (511, code511, mkInitMode511 #[] progPush7Ret 1),
          (511, code511, mkInitMode511 #[] progPush7Ret 2),       -- retVals>depth => stkUnd path
          (511, code511, (mkInitMode511 #[mkIntArg 9] progRet 1)) -- stackSize=1
        ]
    | none => pure ()

    -- mode=510: stress mode (many optional args). These cases intentionally trigger early stkUnd/typeChk paths.
    match code510? with
    | some code510 =>
        cases := cases ++ #[
          (510, code510, #[]),
          (510, code510, #[mkIntArg 0, progRet])
        ]
    | none => pure ()

    cases := cases.take casesWanted

    let oracleInputs : Array (Cell × List String) :=
      cases.map (fun (_mode, code, init) => (code, init.toList.map (·.fift)))
    let oracleOuts ← runOracleBatch oracleInputs

    for cidx in [0:cases.size] do
      let (mode, code, init) := cases[cidx]!
      if verbose then
        let argDump := String.intercalate " " (init.toList.map (·.fift))
        IO.println s!"RUNVM (case {cidx+1}/{cases.size}, mode={mode}): {argDump}"
      let initStack : Array Value := init.map (·.lean)
      let oracle ←
        match oracleOuts[cidx]? with
        | some o => pure o
        | none => die s!"RUNVM (case {cidx+1}, mode={mode}): missing oracle output"
      let leanRes := runLean code initStack
      let (leanExit, stF) ←
        match leanRes with
        | .halt ec st => pure (ec, st)
        | .continue _ => die "RUNVM: Lean did not halt (fuel exhausted)"
      let exitRawLean : Int := ~~~ leanExit
      let gasUsedLean : Int := stF.gas.gasConsumed
      if exitRawLean != oracle.exitRaw then
        die s!"RUNVM (case {cidx+1}, mode={mode}): EXIT mismatch lean_raw={exitRawLean} oracle={oracle.exitRaw} (lean_exit={leanExit})"
      if gasUsedLean != oracle.gasUsed then
        die s!"RUNVM (case {cidx+1}, mode={mode}): GAS mismatch lean={gasUsedLean} oracle={oracle.gasUsed}"
      let c4HashLean : String := hashHex (Cell.hashBytes stF.regs.c4)
      let c5HashLean : String := hashHex (Cell.hashBytes stF.regs.c5)
      if c4HashLean != oracle.c4Hash then
        die s!"RUNVM (case {cidx+1}, mode={mode}): C4 mismatch lean={c4HashLean} oracle={oracle.c4Hash}"
      if c5HashLean != oracle.c5Hash then
        die s!"RUNVM (case {cidx+1}, mode={mode}): C5 mismatch lean={c5HashLean} oracle={oracle.c5Hash}"
      let stackLeanTop : Array String :=
        Array.ofFn (n := stF.stack.size) fun i =>
          canonValue (stF.stack[stF.stack.size - 1 - i.1]!)
      if stackLeanTop.size != oracle.stackTop.size then
        die s!"RUNVM (case {cidx+1}, mode={mode}): DEPTH mismatch lean={stackLeanTop.size} oracle={oracle.stackTop.size}"
      for i in [0:stackLeanTop.size] do
        let a := stackLeanTop[i]!
        let b := oracle.stackTop[i]!
        if a != b then
          die s!"RUNVM (case {cidx+1}, mode={mode}): STACK mismatch at idx={i} lean='{a}' oracle='{b}'"
    return ()

  let (codePairs, variantsAll) ←
    if row.signature == "" then
      -- Stack ops with missing signatures: generate non-underflow stacks based on the opcode parameters.
      let mut kept : Array (Nat × Cell) := #[]
      let mut needMax : Nat := 1
      for (av, c) in codePairs do
        match decodeFirstInstr c with
        | .ok ins =>
            let need := noSigNeedDepth ins
            if need ≤ maxNoSigDepth then
              kept := kept.push (av, c)
              needMax := Nat.max needMax need
        | .error _ =>
            pure ()
      let keptFinal :=
        if kept.isEmpty then
          codePairs.take 1
        else
          kept
      let want : Nat := Nat.max 1 maxStackVariantsPerInstr
      let mut stacks : Array (Array InitArg) :=
        #[
          mkIntStackAsc needMax,
          mkIntStackDesc needMax,
          mkStackMixed needMax
        ]
      if needMax > 0 then
        stacks := stacks.push (mkIntStackAsc (needMax - 1))
      stacks := stacks ++
        #[
          mkIntStackAsc (needMax + 2),
          mkStackMixed (needMax + 2),
          mkIntStackAsc (needMax + 8),
          mkStackMixed (needMax + 8),
          #[]
        ]
      stacks := (stackDedup stacks).take want
      pure (keptFinal, stacks)
    else
      let inputs := sigInputs row.signature
      let vars ← buildVariants inputs (Nat.max 1 maxStackVariantsPerInstr)
      pure (codePairs, vars)

  let stackVariants := variantsAll.take (Nat.max 1 maxStackVariantsPerInstr)
  let defaultCases : Nat :=
    Nat.max 1 (1 + (stackVariants.size - 1) + (codePairs.size - 1))
  let casesPerInstr : Nat := (casesPerInstr?.getD defaultCases) |> Nat.max 1

  let mut cases : Array (Nat × Nat) := #[(0, 0)]
  let mut si : Nat := 1
  let mut cj : Nat := 1
  let mut pickStack : Bool := true
  while cases.size < casesPerInstr && (si < stackVariants.size || cj < codePairs.size) do
    if pickStack && si < stackVariants.size then
      cases := cases.push (0, si)
      si := si + 1
      pickStack := false
    else if (!pickStack) && cj < codePairs.size then
      cases := cases.push (cj, 0)
      cj := cj + 1
      pickStack := true
    else if si < stackVariants.size then
      cases := cases.push (0, si)
      si := si + 1
    else if cj < codePairs.size then
      cases := cases.push (cj, 0)
      cj := cj + 1

  if cases.size < casesPerInstr then
    for i in [1:stackVariants.size] do
      for j in [1:codePairs.size] do
        if cases.size >= casesPerInstr then
          break
        cases := cases.push (j, i)
      if cases.size >= casesPerInstr then
        break

  let oracleInputs : Array (Cell × List String) :=
    Array.ofFn (n := cases.size) fun cidx =>
      let (j, i) := cases[cidx.1]!
      let code := codePairs[j]!.snd
      let init := stackVariants[i]!
      (code, init.toList.map (·.fift))
  let oracleOuts ← runOracleBatch oracleInputs

  for cidx in [0:cases.size] do
    let (j, i) := cases[cidx]!
    let (argsVal, code) := codePairs[j]!
    let init := stackVariants[i]!
    if verbose then
      let argDump := String.intercalate " " (init.toList.map (·.fift))
      IO.println s!"{row.name} (case {cidx+1}/{cases.size}, code {j+1}/{codePairs.size} argsVal=0x{String.mk (Nat.toDigits 16 argsVal)}, stack {i+1}/{stackVariants.size}): {argDump}"
    let initStack : Array Value := init.map (·.lean)
    let oracle ←
      match oracleOuts[cidx]? with
      | some o => pure o
      | none => die s!"{row.name} (case {cidx+1}): missing oracle output"
    let leanRes := runLean code initStack
    let (leanExit, stF) ←
      match leanRes with
      | .halt ec st => pure (ec, st)
      | .continue _ => die s!"{row.name}: Lean did not halt (fuel exhausted)"
    let exitRawLean : Int := ~~~ leanExit
    let gasUsedLean : Int := stF.gas.gasConsumed
    if exitRawLean != oracle.exitRaw then
      die s!"{row.name} (case {cidx+1}): EXIT mismatch lean_raw={exitRawLean} oracle={oracle.exitRaw} (lean_exit={leanExit})"
    if gasUsedLean != oracle.gasUsed then
      die s!"{row.name} (case {cidx+1}): GAS mismatch lean={gasUsedLean} oracle={oracle.gasUsed}"
    let c4HashLean : String := hashHex (Cell.hashBytes stF.regs.c4)
    let c5HashLean : String := hashHex (Cell.hashBytes stF.regs.c5)
    if c4HashLean != oracle.c4Hash then
      die s!"{row.name} (case {cidx+1}): C4 mismatch lean={c4HashLean} oracle={oracle.c4Hash}"
    if c5HashLean != oracle.c5Hash then
      die s!"{row.name} (case {cidx+1}): C5 mismatch lean={c5HashLean} oracle={oracle.c5Hash}"
    let stackLeanTop : Array String :=
      Array.ofFn (n := stF.stack.size) fun i =>
        canonValue (stF.stack[stF.stack.size - 1 - i.1]!)
    if stackLeanTop.size != oracle.stackTop.size then
      die s!"{row.name} (case {cidx+1}): DEPTH mismatch lean={stackLeanTop.size} oracle={oracle.stackTop.size}"
    for i in [0:stackLeanTop.size] do
      let a := stackLeanTop[i]!
      let b := oracle.stackTop[i]!
      if a != b then
        die s!"{row.name} (case {cidx+1}): STACK mismatch at idx={i} lean='{a}' oracle='{b}'"

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
  let codeVariantsPerInstr : Nat :=
    match args.dropWhile (· != "--code-variants") with
    | _ :: n :: _ => n.toNat?.getD 1
    | _ => 1
  let casesPerInstr? : Option Nat :=
    match args.dropWhile (· != "--cases") with
    | _ :: n :: _ => n.toNat?
    | _ => none
  let maxNoSigDepth : Nat :=
    match args.dropWhile (· != "--max-nosig-depth") with
    | _ :: n :: _ => n.toNat?.getD 64
    | _ => 64
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
    validateRow r variantsPerInstr codeVariantsPerInstr casesPerInstr? verbose maxNoSigDepth

  IO.println "ok"
  return 0

end TvmLeanOracleValidate

def main (args : List String) : IO UInt32 :=
  TvmLeanOracleValidate.main args
