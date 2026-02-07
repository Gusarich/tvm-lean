import Lean
import TvmLean
import TvmLean.Native

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

def cell3 : Cell :=
  -- 6 bits: 110010
  Cell.mkOrdinary #[true, true, false, false, true, false] #[]

def cell4 : Cell :=
  -- 9 bits: 101101001
  Cell.mkOrdinary #[true, false, true, true, false, true, false, false, true] #[]

def cellRef1 : Cell :=
  -- Small cell with one reference.
  Cell.mkOrdinary #[false, true, true, false] #[cell1]

def cellRef2 : Cell :=
  -- Small cell with two references.
  Cell.mkOrdinary #[true, false, false, true, true] #[cell1, cell2]

def slice1 : Slice :=
  Slice.ofCell cell1

def slice2 : Slice :=
  Slice.ofCell cell2

def slice3 : Slice :=
  Slice.ofCell cell3

def slice4 : Slice :=
  Slice.ofCell cell4

def builder1 : Builder :=
  Builder.empty.storeBits #[true]

def builder2 : Builder :=
  Builder.empty.storeBits #[true, false, true, false]

def builder3 : Builder :=
  Builder.empty.storeBits #[true, true, false, false, true, false]

def builder4 : Builder :=
  Builder.empty.storeBits #[true, false, true, true, false, true, false, false, true]

def tuple1 : Array Value :=
  #[.int (.num 1)]

def tuple2 : Array Value :=
  #[.int (.num 1), .int (.num 2)]

def tuple3 : Array Value :=
  #[.cell cell1, .int (.num (-1)), .slice slice2]

def tuple4 : Array Value :=
  #[.cell cell3, .slice slice3, .cont (.quit 3), .int (.num 42)]

def cellToBocHex? (c : Cell) : Option String :=
  match stdBocSerialize c with
  | .ok bytes => some (bytesToHex bytes)
  | .error _ => none

def mkCellArgBoc (c : Cell) : InitArg :=
  match cellToBocHex? c with
  | some hex => { fift := s!"CB:{hex}", lean := .cell c }
  | none => { fift := "C1", lean := .cell cell1 }

def mkSliceArgBoc (c : Cell) : InitArg :=
  match cellToBocHex? c with
  | some hex => { fift := s!"SB:{hex}", lean := .slice (Slice.ofCell c) }
  | none => { fift := "S1", lean := .slice slice1 }

def cellBocArg1 : InitArg := mkCellArgBoc cellRef1
def cellBocArg2 : InitArg := mkCellArgBoc cellRef2
def sliceBocArg1 : InitArg := mkSliceArgBoc cellRef1
def sliceBocArg2 : InitArg := mkSliceArgBoc cellRef2

private def cellFromBocBase64Or (b64 : String) (fallback : Cell := cell1) : Cell :=
  match decodeCellBoc b64 with
  | .ok c => c
  | .error _ => fallback

def malformedDictCell1 : Cell :=
  -- Hex BOC: b5ee9c7201010301000b0002019c01020001c00001a8
  cellFromBocBase64Or "te6ccgEBAwEACwACAZwBAgABwAABqA=="

def malformedDictCell2 : Cell :=
  -- Hex BOC: b5ee9c7201010201000700010168010001c0
  cellFromBocBase64Or "te6ccgEBAgEABwABAWgBAAHA"

def malformedDictCellArg1 : InitArg :=
  { fift := "CB:b5ee9c7201010301000b0002019c01020001c00001a8", lean := .cell malformedDictCell1 }

def malformedDictCellArg2 : InitArg :=
  { fift := "CB:b5ee9c7201010201000700010168010001c0", lean := .cell malformedDictCell2 }

def malformedDictSliceArg1 : InitArg :=
  { fift := "SB:b5ee9c7201010301000b0002019c01020001c00001a8", lean := .slice (Slice.ofCell malformedDictCell1) }

def malformedDictSliceArg2 : InitArg :=
  { fift := "SB:b5ee9c7201010201000700010168010001c0", lean := .slice (Slice.ofCell malformedDictCell2) }

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

def mkStackTypedCycle (depth : Nat) : Array InitArg :=
  let pool : Array InitArg :=
    #[
      mkIntArg 0,
      mkIntArg 1,
      mkIntArg (-1),
      { fift := "N", lean := .null },
      { fift := "C1", lean := .cell cell1 },
      { fift := "S1", lean := .slice slice1 },
      { fift := "B1", lean := .builder builder1 },
      { fift := "T1", lean := .tuple tuple1 },
      { fift := "K1", lean := .cont (.quit 1) },
      cellBocArg1,
      sliceBocArg1,
      malformedDictCellArg1,
      malformedDictSliceArg1
    ]
  Array.ofFn (n := depth) fun i =>
    pool[i.1 % pool.size]!

def mkStackHetero (depth : Nat) : Array InitArg :=
  let base := mkIntStackDesc depth
  let base :=
    if depth > 0 then
      base.set! (depth - 1) { fift := "N", lean := .null }
    else
      base
  let base :=
    if depth > 1 then
      base.set! (depth - 2) cellBocArg1
    else
      base
  let base :=
    if depth > 2 then
      base.set! (depth - 3) sliceBocArg1
    else
      base
  let base :=
    if depth > 3 then
      base.set! (depth - 4) { fift := "B4", lean := .builder builder4 }
    else
      base
  let base :=
    if depth > 4 then
      base.set! (depth - 5) { fift := "T4", lean := .tuple tuple4 }
    else
      base
  let base :=
    if depth > 5 then
      base.set! (depth - 6) { fift := "K4", lean := .cont (.quit 4) }
    else
      base
  let base :=
    if depth > 6 then
      base.set! (depth - 7) malformedDictCellArg1
    else
      base
  let base :=
    if depth > 7 then
      base.set! (depth - 8) malformedDictSliceArg1
    else
      base
  base

def intPow2Near (k : Nat) : List Int :=
  let p : Int := Int.ofNat (1 <<< k)
  [p - 1, p, -(p), -(p - 1)]

def mkInitArgVariants (nm ty : String) : Option (Array InitArg) :=
  match ty with
  | "Int" =>
      let base : Int := if nm == "p" || nm == "r" || nm == "n" then 0 else 1
      let minInt257 : Int := -(Int.ofNat (1 <<< 256))
      let maxInt257 : Int := (Int.ofNat (1 <<< 256)) - 1
      let pows : List Nat := [7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255]
      let edgePows : List Int := pows.flatMap intPow2Near
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
          -255,
          -256,
          256,
          1023,
          -1024,
          4095,
          -4096,
          65535,
          -65536,
          maxInt257,
          maxInt257 - 1,
          maxInt257 - 2,
          minInt257
        ] ++ edgePows ++ [minInt257 + 1, minInt257 + 2]).eraseDups
      let nums : Array InitArg :=
        vals.toArray.map (fun n => { fift := toString n, lean := .int (.num n) })
      some nums
  | "Bool" =>
      some #[
        { fift := "0", lean := .int (.num 0) },
        { fift := "1", lean := .int (.num 1) },
        { fift := "-1", lean := .int (.num (-1)) },
        { fift := "2", lean := .int (.num 2) },
        { fift := "-2", lean := .int (.num (-2)) },
        { fift := "127", lean := .int (.num 127) },
        { fift := "-128", lean := .int (.num (-128)) }
      ]
  | "Any" =>
      let minInt257 : Int := -(Int.ofNat (1 <<< 256))
      let maxInt257 : Int := (Int.ofNat (1 <<< 256)) - 1
      some #[
        { fift := "0", lean := .int (.num 0) },
        { fift := "1", lean := .int (.num 1) },
        { fift := "-1", lean := .int (.num (-1)) },
        { fift := "127", lean := .int (.num 127) },
        { fift := "-128", lean := .int (.num (-128)) },
        { fift := "65535", lean := .int (.num 65535) },
        { fift := "-65536", lean := .int (.num (-65536)) },
        { fift := toString maxInt257, lean := .int (.num maxInt257) },
        { fift := toString minInt257, lean := .int (.num minInt257) },
        { fift := "N", lean := .null },
        { fift := "C", lean := .cell Cell.empty },
        { fift := "C1", lean := .cell cell1 },
        { fift := "C2", lean := .cell cell2 },
        { fift := "C3", lean := .cell cell3 },
        { fift := "C4", lean := .cell cell4 },
        cellBocArg1,
        cellBocArg2,
        { fift := "S", lean := .slice emptySlice },
        { fift := "S1", lean := .slice slice1 },
        { fift := "S2", lean := .slice slice2 },
        { fift := "S3", lean := .slice slice3 },
        { fift := "S4", lean := .slice slice4 },
        sliceBocArg1,
        sliceBocArg2,
        { fift := "B", lean := .builder emptyBuilder },
        { fift := "B1", lean := .builder builder1 },
        { fift := "B2", lean := .builder builder2 },
        { fift := "B3", lean := .builder builder3 },
        { fift := "B4", lean := .builder builder4 },
        { fift := "T", lean := .tuple #[] },
        { fift := "T1", lean := .tuple tuple1 },
        { fift := "T2", lean := .tuple tuple2 },
        { fift := "T3", lean := .tuple tuple3 },
        { fift := "T4", lean := .tuple tuple4 },
        { fift := "K", lean := .cont (.quit 0) },
        { fift := "K1", lean := .cont (.quit 1) },
        { fift := "K2", lean := .cont (.quit 2) },
        { fift := "K3", lean := .cont (.quit 3) },
        { fift := "K4", lean := .cont (.quit 4) }
      ]
  | "Cell" =>
      some #[
        { fift := "C", lean := .cell Cell.empty },
        { fift := "C1", lean := .cell cell1 },
        { fift := "C2", lean := .cell cell2 },
        { fift := "C3", lean := .cell cell3 },
        { fift := "C4", lean := .cell cell4 },
        cellBocArg1,
        cellBocArg2
      ]
  | "Slice" =>
      some #[
        { fift := "S", lean := .slice emptySlice },
        { fift := "S1", lean := .slice slice1 },
        { fift := "S2", lean := .slice slice2 },
        { fift := "S3", lean := .slice slice3 },
        { fift := "S4", lean := .slice slice4 },
        sliceBocArg1,
        sliceBocArg2
      ]
  | "Builder" =>
      some #[
        { fift := "B", lean := .builder emptyBuilder },
        { fift := "B1", lean := .builder builder1 },
        { fift := "B2", lean := .builder builder2 },
        { fift := "B3", lean := .builder builder3 },
        { fift := "B4", lean := .builder builder4 }
      ]
  | "Tuple" =>
      some #[
        { fift := "T", lean := .tuple #[] },
        { fift := "T1", lean := .tuple tuple1 },
        { fift := "T2", lean := .tuple tuple2 },
        { fift := "T3", lean := .tuple tuple3 },
        { fift := "T4", lean := .tuple tuple4 }
      ]
  | "Continuation" =>
      some #[
        { fift := "K", lean := .cont (.quit 0) },
        { fift := "K1", lean := .cont (.quit 1) },
        { fift := "K2", lean := .cont (.quit 2) },
        { fift := "K3", lean := .cont (.quit 3) },
        { fift := "K4", lean := .cont (.quit 4) }
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

def bitPattern (len : Nat) (firstOne : Bool) : Nat :=
  Id.run do
    let mut out : Nat := 0
    for i in [0:len] do
      out := out <<< 1
      let bit := if i % 2 == 0 then firstOne else !firstOne
      if bit then
        out := out ||| 1
    out

def repValsUnsignedBits (len : Nat) : Array Int :=
  if len == 0 then
    #[0]
  else
    let maxU : Nat := (1 <<< len) - 1
    let altA : Nat := bitPattern len true &&& maxU
    let altB : Nat := bitPattern len false &&& maxU
    let mid : Nat := maxU / 2
    let cands : List Int :=
      [0, 1, Int.ofNat altA, Int.ofNat altB, Int.ofNat mid, Int.ofNat (maxU - 1), Int.ofNat maxU]
    cands.eraseDups.toArray

def repValsForField (f : ImmField) : Array Int :=
  match f.range? with
  | some (minI, maxI) =>
      if f.tag == "int" || f.tag == "tinyInt" then
        repValsSigned minI maxI
      else
        repValsUnsigned minI maxI
  | none =>
      if f.len == 0 then
        #[0]
      else if f.tag == "int" || f.tag == "tinyInt" then
        let minI : Int := -(Int.ofNat (1 <<< (f.len - 1)))
        let maxI : Int := (Int.ofNat (1 <<< (f.len - 1))) - 1
        repValsSigned minI maxI
      else
        repValsUnsignedBits f.len

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

def buildArgsValVariants (row : InstrRow) (maxCodeVariants : Nat) (randomCases : Nat := 0)
    (seed : UInt64 := 1) : Except String (Array Nat) := do
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
    let alts : Array Int := repValsForField f
    for v in alts do
      if out.size >= maxCodeVariants then
        break
      if v == baseVals[i]! then
        continue
      let vals' := baseVals.set! i v
      let av ← packArgsVal fields vals'
      if !(out.contains av) then
        out := out.push av

  -- Dense single-field sweeps for compact immediate domains.
  let denseValsForField (f : ImmField) : Array Int :=
    match f.range? with
    | some (minI, maxI) =>
        if minI ≤ maxI && (maxI - minI).toNat ≤ 512 then
          let span : Nat := (maxI - minI).toNat + 1
          Array.ofFn (n := span) fun k => minI + Int.ofNat k
        else
          #[]
    | none =>
        if f.len ≤ 8 then
          let span : Nat := 1 <<< f.len
          Array.ofFn (n := span) fun k => Int.ofNat k
        else
          #[]
  if out.size < maxCodeVariants then
    for i in [0:fields.size] do
      if out.size >= maxCodeVariants then
        break
      let f := fields[i]!
      let dense := denseValsForField f
      if !dense.isEmpty then
        for v in dense do
          if out.size >= maxCodeVariants then
            break
          if v == baseVals[i]! then
            continue
          let vals' := baseVals.set! i v
          let av ← packArgsVal fields vals'
          if !(out.contains av) then
            out := out.push av

  -- Pairwise field interaction coverage.
  if out.size < maxCodeVariants && fields.size ≥ 2 then
    let fieldVals : Array (Array Int) := Array.ofFn (n := fields.size) fun i => repValsForField fields[i.1]!
    for i in [0:fields.size] do
      if out.size >= maxCodeVariants then
        break
      for j in [i+1:fields.size] do
        if out.size >= maxCodeVariants then
          break
        let ai := (fieldVals[i]!).take 4
        let aj := (fieldVals[j]!).take 4
        for vi in ai do
          if out.size >= maxCodeVariants then
            break
          for vj in aj do
            if out.size >= maxCodeVariants then
              break
            if vi == baseVals[i]! && vj == baseVals[j]! then
              continue
            let vals' := (baseVals.set! i vi).set! j vj
            let av ← packArgsVal fields vals'
            if !(out.contains av) then
              out := out.push av

  -- Dense pairwise sweeps for compact immediate domains (captures mode-flag interactions).
  if out.size < maxCodeVariants && fields.size ≥ 2 then
    let denseByField : Array (Array Int) := Array.ofFn (n := fields.size) fun i =>
      denseValsForField fields[i.1]!
    for i in [0:fields.size] do
      if out.size >= maxCodeVariants then
        break
      for j in [i+1:fields.size] do
        if out.size >= maxCodeVariants then
          break
        let di := denseByField[i]!
        let dj := denseByField[j]!
        if !di.isEmpty && !dj.isEmpty && di.size ≤ 16 && dj.size ≤ 16 then
          for vi in di do
            if out.size >= maxCodeVariants then
              break
            for vj in dj do
              if out.size >= maxCodeVariants then
                break
              if vi == baseVals[i]! && vj == baseVals[j]! then
                continue
              let vals' := (baseVals.set! i vi).set! j vj
              let av ← packArgsVal fields vals'
              if !(out.contains av) then
                out := out.push av

  -- Dense triple sweeps for compact immediate domains (non-linear mode interactions).
  if out.size < maxCodeVariants && fields.size ≥ 3 then
    let denseByField : Array (Array Int) := Array.ofFn (n := fields.size) fun i =>
      denseValsForField fields[i.1]!
    for i in [0:fields.size] do
      if out.size >= maxCodeVariants then
        break
      for j in [i+1:fields.size] do
        if out.size >= maxCodeVariants then
          break
        for k in [j+1:fields.size] do
          if out.size >= maxCodeVariants then
            break
          let di := denseByField[i]!
          let dj := denseByField[j]!
          let dk := denseByField[k]!
          if !di.isEmpty && !dj.isEmpty && !dk.isEmpty && di.size ≤ 8 && dj.size ≤ 8 && dk.size ≤ 8 then
            for vi in di do
              if out.size >= maxCodeVariants then
                break
              for vj in dj do
                if out.size >= maxCodeVariants then
                  break
                for vk in dk do
                  if out.size >= maxCodeVariants then
                    break
                  if vi == baseVals[i]! && vj == baseVals[j]! && vk == baseVals[k]! then
                    continue
                  let vals' := ((baseVals.set! i vi).set! j vj).set! k vk
                  let av ← packArgsVal fields vals'
                  if !(out.contains av) then
                    out := out.push av

  -- Exhaustive full-vector sweep when all immediate domains are compact.
  if out.size < maxCodeVariants && fields.size > 0 then
    let denseByField : Array (Array Int) := Array.ofFn (n := fields.size) fun i =>
      denseValsForField fields[i.1]!
    let fullCap : Nat := Nat.min maxCodeVariants 4096
    let mut canExhaustive := true
    let mut prod : Nat := 1
    let mut fullVals : Array (Array Int) := #[]
    for i in [0:fields.size] do
      let d := denseByField[i]!
      if d.isEmpty then
        canExhaustive := false
      else if canExhaustive then
        let newProd := prod * d.size
        if newProd > fullCap then
          canExhaustive := false
        else
          prod := newProd
      fullVals := fullVals.push d
    if canExhaustive && prod > 0 then
      let mut idxs : Array Nat := Array.replicate fields.size 0
      let mut done := false
      while !done && out.size < maxCodeVariants do
        let mut vals := baseVals
        for i in [0:fields.size] do
          let vi := (fullVals[i]!)[idxs[i]!]!
          vals := vals.set! i vi
        let av ← packArgsVal fields vals
        if !(out.contains av) then
          out := out.push av
        let mut pos := fields.size
        let mut advanced := false
        while !advanced do
          if pos == 0 then
            done := true
            advanced := true
          else
            let pos' := pos - 1
            let cur := idxs[pos']!
            let lim := (fullVals[pos']!).size
            if cur + 1 < lim then
              idxs := idxs.set! pos' (cur + 1)
              for t in [pos'+1:fields.size] do
                idxs := idxs.set! t 0
              advanced := true
            else
              pos := pos'

  -- Whole-vector extremes to stress multi-bit mode combinations.
  if out.size < maxCodeVariants && fields.size > 0 then
    let fieldVals : Array (Array Int) := Array.ofFn (n := fields.size) fun i => repValsForField fields[i.1]!
    let mut lo := baseVals
    let mut hi := baseVals
    let mut zig := baseVals
    for i in [0:fields.size] do
      let vs := fieldVals[i]!
      if !vs.isEmpty then
        let vLo := vs[0]!
        let vHi := vs[vs.size - 1]!
        lo := lo.set! i vLo
        hi := hi.set! i vHi
        zig := zig.set! i (if i % 2 == 0 then vLo else vHi)
    let loAv ← packArgsVal fields lo
    if !(out.contains loAv) then
      out := out.push loAv
    if out.size < maxCodeVariants then
      let hiAv ← packArgsVal fields hi
      if !(out.contains hiAv) then
        out := out.push hiAv
    if out.size < maxCodeVariants then
      let zigAv ← packArgsVal fields zig
      if !(out.contains zigAv) then
        out := out.push zigAv

  -- Seeded random combos of immediate fields (cross-field diversity beyond pairwise anchors).
  let randomBudget : Nat := Nat.min randomCases (maxCodeVariants * 32 + 1024)
  if out.size < maxCodeVariants && randomBudget > 0 && fields.size > 0 then
    let fieldVals : Array (Array Int) := Array.ofFn (n := fields.size) fun i => repValsForField fields[i.1]!
    let seedBase : Nat :=
      Id.run do
        let mut h : Nat := seed.toNat + 1
        for c in row.name.data do
          h := (h * 16777619 + c.toNat + 1013904223) % (1 <<< 63)
        h
    let mut spins : Nat := 0
    let budget : Nat := randomBudget * 2 + 64
    while out.size < maxCodeVariants && spins < budget do
      let mut vals := baseVals
      for i in [0:fields.size] do
        let vs := fieldVals[i]!
        if !vs.isEmpty then
          let mix : Nat := seedBase + (spins + 1) * 1103515245 + (i + 1) * 12345
          let k : Nat := mix % vs.size
          vals := vals.set! i vs[k]!
      let av ← packArgsVal fields vals
      if !(out.contains av) then
        out := out.push av
      spins := spins + 1

  -- RNG-driven immediate sampling with single/pair/all-field perturbations.
  if out.size < maxCodeVariants && randomBudget > 0 && fields.size > 0 then
    let fieldVals : Array (Array Int) := Array.ofFn (n := fields.size) fun i => repValsForField fields[i.1]!
    let seedBase2 : Nat :=
      Id.run do
        let mut h : Nat := seed.toNat + 0x9e3779b9
        for c in row.name.data do
          h := (h * 1664525 + c.toNat + 1013904223) % (1 <<< 63)
        h
    let mut spins : Nat := 0
    let budget : Nat := randomBudget * 4 + 128
    while out.size < maxCodeVariants && spins < budget do
      let mode : Nat := (seedBase2 + (spins + 1) * 1103515245) % 5
      let mut vals := baseVals
      if mode == 0 then
        -- Randomize all fields.
        for i in [0:fields.size] do
          let vs := fieldVals[i]!
          if !vs.isEmpty then
            let mix : Nat := seedBase2 + (spins + 1) * 1664525 + (i + 1) * 1013904223
            let k : Nat := mix % vs.size
            vals := vals.set! i vs[k]!
      else if mode == 1 then
        -- Randomize one field only.
        let fi : Nat := (seedBase2 + (spins + 1) * 22695477) % fields.size
        let vs := fieldVals[fi]!
        if !vs.isEmpty then
          let k : Nat := (seedBase2 + (spins + 1) * 69069 + fi * 362437) % vs.size
          vals := vals.set! fi vs[k]!
      else if mode == 2 then
        -- Randomize two fields.
        let fi : Nat := (seedBase2 + (spins + 1) * 48271) % fields.size
        let fj : Nat := (seedBase2 + (spins + 1) * 214013 + 2531011) % fields.size
        let vsi := fieldVals[fi]!
        let vsj := fieldVals[fj]!
        if !vsi.isEmpty then
          let ki : Nat := (seedBase2 + (spins + 1) * 134775813 + fi * 17) % vsi.size
          vals := vals.set! fi vsi[ki]!
        if !vsj.isEmpty then
          let kj : Nat := (seedBase2 + (spins + 1) * 1103515245 + fj * 31 + 12345) % vsj.size
          vals := vals.set! fj vsj[kj]!
      else if mode == 3 then
        -- Alternate low/high anchors across fields.
        for i in [0:fields.size] do
          let vs := fieldVals[i]!
          if !vs.isEmpty then
            let v := if i % 2 == 0 then vs[0]! else vs[vs.size - 1]!
            vals := vals.set! i v
      else
        -- Keep one random field at base, randomize the rest.
        let keepI : Nat := (seedBase2 + (spins + 1) * 2654435761) % fields.size
        for i in [0:fields.size] do
          if i != keepI then
            let vs := fieldVals[i]!
            if !vs.isEmpty then
              let k : Nat := (seedBase2 + (spins + 1) * 3935559000370003845 + (i + 1) * 6364136223846793005) % vs.size
              vals := vals.set! i vs[k]!
      let av ← packArgsVal fields vals
      if !(out.contains av) then
        out := out.push av
      spins := spins + 1

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

def buildCodeCells (row : InstrRow) (maxCodeVariants : Nat) (randomCases : Nat := 0)
    (seed : UInt64 := 1) : Except String (Array (Nat × Cell)) := do
  let maxCodeVariants := Nat.max 1 maxCodeVariants
  let argsVals ← buildArgsValVariants row maxCodeVariants randomCases seed
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
  let oracleLib := (← IO.getEnv "TVMLEANTON_ORACLE_LIB_FIF").getD "oracle/fif/ton_oracle_runvm_lib.fif"
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
  let oracleScript := (← IO.getEnv "TVMLEANTON_ORACLE_FIF").getD "oracle/fif/ton_oracle_runvm.fif"
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
    -- Standard deterministic c7 context (must match `oracle/fif/ton_oracle_runvm.fif`).
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
      match stCur.step nativeHost with
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

def leanOutCells (st : VmState) : Cell × Cell :=
  -- Oracle `runvmx(mode=60)` exposes committed output cells:
  -- return `null` for c4/c5 when no commit happened, which our parser
  -- normalizes to the empty-cell hash.
  if st.cstate.committed then
    (st.cstate.c4, st.cstate.c5)
  else
    (Cell.empty, Cell.empty)

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

structure Rng64 where
  state : UInt64
  deriving Inhabited

def Rng64.next (r : Rng64) : UInt64 × Rng64 :=
  let s' : UInt64 := r.state * 6364136223846793005 + 1442695040888963407
  (s', { state := s' })

def Rng64.nextNat (r : Rng64) (bound : Nat) : Nat × Rng64 :=
  if bound == 0 then
    (0, r)
  else
    let (x, r') := r.next
    (x.toNat % bound, r')

def mixSeed (baseSeed : UInt64) (tag : String) : UInt64 :=
  Id.run do
    let mut h : UInt64 := baseSeed ^^^ 1469598103934665603
    for c in tag.data do
      h := (h ^^^ UInt64.ofNat c.toNat) * 1099511628211
    if h == 0 then
      1
    else
      h

def interleaveArrays (a b : Array α) : Array α :=
  Id.run do
    let mut out : Array α := #[]
    let n := Nat.max a.size b.size
    for i in [0:n] do
      if h : i < a.size then
        out := out.push (a[i]'h)
      if h : i < b.size then
        out := out.push (b[i]'h)
    out

def pushIfFresh (out : Array (Array InitArg)) (st : Array InitArg) : Array (Array InitArg) :=
  if out.any (fun st' => stackKey st' == stackKey st) then
    out
  else
    out.push st

def randIntBases : Array Int :=
  #[
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
    15,
    -15,
    31,
    -31,
    63,
    -63,
    127,
    -127,
    255,
    -255,
    1023,
    -1023,
    4095,
    -4095,
    (Int.ofNat (1 <<< 31)) - 1,
    -(Int.ofNat (1 <<< 31)),
    (Int.ofNat (1 <<< 63)) - 1,
    -(Int.ofNat (1 <<< 63)),
    (Int.ofNat (1 <<< 127)) - 1,
    -(Int.ofNat (1 <<< 127)),
    (Int.ofNat (1 <<< 255)) - 1,
    -(Int.ofNat (1 <<< 255)),
    (Int.ofNat (1 <<< 256)) - 1,
    -(Int.ofNat (1 <<< 256))
  ]

def randAtomPool : Array InitArg :=
  #[
    { fift := "N", lean := .null },
    { fift := "C", lean := .cell Cell.empty },
    { fift := "C1", lean := .cell cell1 },
    { fift := "C2", lean := .cell cell2 },
    { fift := "C3", lean := .cell cell3 },
    { fift := "C4", lean := .cell cell4 },
    cellBocArg1,
    cellBocArg2,
    { fift := "S", lean := .slice emptySlice },
    { fift := "S1", lean := .slice slice1 },
    { fift := "S2", lean := .slice slice2 },
    { fift := "S3", lean := .slice slice3 },
    { fift := "S4", lean := .slice slice4 },
    sliceBocArg1,
    sliceBocArg2,
    { fift := "B", lean := .builder emptyBuilder },
    { fift := "B1", lean := .builder builder1 },
    { fift := "B2", lean := .builder builder2 },
    { fift := "B3", lean := .builder builder3 },
    { fift := "B4", lean := .builder builder4 },
    { fift := "T", lean := .tuple #[] },
    { fift := "T1", lean := .tuple tuple1 },
    { fift := "T2", lean := .tuple tuple2 },
    { fift := "T3", lean := .tuple tuple3 },
    { fift := "T4", lean := .tuple tuple4 },
    { fift := "K", lean := .cont (.quit 0) },
    { fift := "K1", lean := .cont (.quit 1) },
    { fift := "K2", lean := .cont (.quit 2) },
    { fift := "K3", lean := .cont (.quit 3) },
    { fift := "K4", lean := .cont (.quit 4) }
  ]

def clampInt257 (x : Int) : Int :=
  let minInt257 : Int := -(Int.ofNat (1 <<< 256))
  let maxInt257 : Int := (Int.ofNat (1 <<< 256)) - 1
  if x < minInt257 then minInt257 else if x > maxInt257 then maxInt257 else x

def randWideNat257 (rng0 : Rng64) : Nat × Rng64 :=
  let (a, rng1) := rng0.next
  let (b, rng2) := rng1.next
  let (c, rng3) := rng2.next
  let (d, rng4) := rng3.next
  let (bits, rng5) := rng4.nextNat 257
  let raw : Nat := (a.toNat <<< 192) + (b.toNat <<< 128) + (c.toNat <<< 64) + d.toNat
  let n : Nat :=
    if bits == 0 then
      0
    else if bits >= 256 then
      raw
    else
      raw &&& ((1 <<< bits) - 1)
  (n, rng5)

def randIntArg (rng0 : Rng64) : InitArg × Rng64 :=
  let (mode, rng1) := rng0.nextNat 8
  if mode < 4 then
    let (bi, rng2) := rng1.nextNat randIntBases.size
    let base := randIntBases[bi]!
    let (dj, rng3) := rng2.nextNat 17
    let delta : Int := Int.ofNat dj - 8
    (mkIntArg (clampInt257 (base + delta)), rng3)
  else if mode < 6 then
    let (k, rng2) := rng1.nextNat 257
    let (d, rng3) := rng2.nextNat 65
    let (sgn, rng4) := rng3.nextNat 2
    let p : Int := Int.ofNat (1 <<< k)
    let x : Int := if sgn == 0 then p - Int.ofNat d else -(p - Int.ofNat d)
    (mkIntArg (clampInt257 x), rng4)
  else if mode == 6 then
    let (n, rng2) := randWideNat257 rng1
    let (sgn, rng3) := rng2.nextNat 2
    let x : Int := if sgn == 0 then Int.ofNat n else -(Int.ofNat n)
    (mkIntArg (clampInt257 x), rng3)
  else
    let extremes : Array Int :=
      #[
        (Int.ofNat (1 <<< 256)) - 1,
        (Int.ofNat (1 <<< 256)) - 2,
        (Int.ofNat (1 <<< 255)),
        0,
        -1,
        -(Int.ofNat (1 <<< 255)),
        -(Int.ofNat (1 <<< 256)) + 1,
        -(Int.ofNat (1 <<< 256))
      ]
    let (ei, rng2) := rng1.nextNat extremes.size
    (mkIntArg extremes[ei]!, rng2)

def randAtomArg (rng0 : Rng64) : InitArg × Rng64 :=
  let (k, rng1) := rng0.nextNat 16
  if k < 8 then
    randIntArg rng1
  else
    let (i, rng2) := rng1.nextNat randAtomPool.size
    (randAtomPool[i]!, rng2)

def randPrefix (rng0 : Rng64) : Array InitArg × Rng64 :=
  let (len0, rng1) := rng0.nextNat 65
  let len := if len0 == 0 then 0 else len0 - 1
  Id.run do
    let mut rng := rng1
    let mut out : Array InitArg := #[]
    for _ in [0:len] do
      let (a, rng') := randAtomArg rng
      out := out.push a
      rng := rng'
    (out, rng)

def randTypedCore (varsPerArg : Array (String × Array InitArg)) (rng0 : Rng64) : Array InitArg × Rng64 :=
  Id.run do
    let mut rng := rng0
    let mut out : Array InitArg := #[]
    for i in [0:varsPerArg.size] do
      let vs := varsPerArg[i]!.snd
      let (k, rng') := rng.nextNat vs.size
      out := out.push vs[k]!
      rng := rng'
    (out, rng)

def randTypedCoreAnchored (varsPerArg : Array (String × Array InitArg)) (rng0 : Rng64) :
    Array InitArg × Rng64 :=
  Id.run do
    let mkAnchors (n : Nat) : Array Nat :=
      if n == 0 then
        #[]
      else
        let raw : Array Nat := #[0, 1, 2, n / 2, n - 3, n - 2, n - 1]
        Id.run do
          let mut outA : Array Nat := #[]
          for x in raw do
            if x < n && !(outA.contains x) then
              outA := outA.push x
          outA
    let mut rng := rng0
    let mut out : Array InitArg := #[]
    for i in [0:varsPerArg.size] do
      let vs := varsPerArg[i]!.snd
      let anchors := mkAnchors vs.size
      if anchors.isEmpty then
        out := out.push vs[0]!
      else
        let (k, rng') := rng.nextNat anchors.size
        let idx := anchors[k]!
        out := out.push vs[idx]!
        rng := rng'
    (out, rng)

def randStack (rng0 : Rng64) (minDepth : Nat) (maxDepth : Nat) : Array InitArg × Rng64 :=
  let lo := minDepth
  let hi := Nat.max lo maxDepth
  let span := (hi - lo) + 1
  let (off, rng1) := rng0.nextNat span
  let depth := lo + off
  Id.run do
    let mut rng := rng1
    let mut out : Array InitArg := #[]
    for _ in [0:depth] do
      let (a, rng') := randAtomArg rng
      out := out.push a
      rng := rng'
    (out, rng)

def noisePrefixes : Array (Array InitArg) :=
  #[
    #[],
    #[mkIntArg 111],
    #[mkIntArg (-111)],
    #[mkIntArg 111, mkIntArg 222],
    #[{ fift := "C1", lean := .cell cell1 }],
    #[{ fift := "C3", lean := .cell cell3 }],
    #[cellBocArg1],
    #[mkIntArg 111, { fift := "C1", lean := .cell cell1 }],
    #[mkIntArg 111, { fift := "S3", lean := .slice slice3 }],
    #[mkIntArg 111, { fift := "S2", lean := .slice slice2 }],
    #[
      { fift := "S1", lean := .slice slice1 },
      { fift := "B1", lean := .builder builder1 },
      { fift := "T1", lean := .tuple tuple1 }
    ],
    #[
      sliceBocArg1,
      { fift := "B3", lean := .builder builder3 },
      { fift := "T3", lean := .tuple tuple3 }
    ],
    #[{ fift := "K1", lean := .cont (.quit 1) }],
    #[{ fift := "K4", lean := .cont (.quit 4) }],
    #[mkIntArg 111, { fift := "S1", lean := .slice slice1 }, { fift := "C1", lean := .cell cell1 }]
  ]

def buildNoInputStacks (max : Nat) (randomCases : Nat := 0) (seed : UInt64 := 1) : Array (Array InitArg) :=
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
      mkIntStackDesc 16,
      mkIntStackAsc 24,
      mkIntStackDesc 24,
      mkStackMixed 24,
      mkIntStackAsc 32,
      mkIntStackDesc 32,
      mkStackMixed 32,
      mkIntStackAsc 48,
      mkIntStackDesc 48,
      mkStackMixed 48,
      mkIntStackAsc 64,
      mkIntStackDesc 64,
      mkStackMixed 64,
      mkStackTypedCycle 64,
      mkStackHetero 64,
      mkIntStackAsc 96,
      mkIntStackDesc 96,
      mkStackMixed 96,
      mkStackTypedCycle 96,
      mkStackHetero 96,
      mkIntStackAsc 128,
      mkIntStackDesc 128,
      mkStackMixed 128,
      mkStackTypedCycle 128,
      mkStackHetero 128,
      mkIntStackAsc 160,
      mkIntStackDesc 160,
      mkStackMixed 160,
      mkStackTypedCycle 160,
      mkStackHetero 160,
      mkIntStackAsc 192,
      mkIntStackDesc 192,
      mkStackMixed 192,
      mkStackTypedCycle 192,
      mkStackHetero 192,
      #[
        { fift := "N", lean := .null },
        mkIntArg 0,
        { fift := "C1", lean := .cell cell1 },
        { fift := "S1", lean := .slice slice1 },
        { fift := "B1", lean := .builder builder1 },
        { fift := "T1", lean := .tuple tuple1 },
        { fift := "K1", lean := .cont (.quit 1) }
      ],
      #[
        malformedDictCellArg1,
        malformedDictSliceArg1,
        mkIntArg 257,
        mkIntArg (-1),
        { fift := "N", lean := .null }
      ],
      #[
        malformedDictCellArg2,
        malformedDictSliceArg2,
        mkIntArg 0,
        { fift := "K4", lean := .cont (.quit 4) },
        { fift := "T4", lean := .tuple tuple4 }
      ],
      #[mkIntArg ((Int.ofNat (1 <<< 63)) - 1)],
      #[mkIntArg (-(Int.ofNat (1 <<< 63)))],
      #[mkIntArg ((Int.ofNat (1 <<< 255)) - 1)],
      #[mkIntArg (-(Int.ofNat (1 <<< 255)))],
      #[mkIntArg 0, mkIntArg 1, mkIntArg 2, mkIntArg 3, mkIntArg 4],
      #[{ fift := "C2", lean := .cell cell2 }, { fift := "S2", lean := .slice slice2 }, { fift := "B2", lean := .builder builder2 }],
      #[{ fift := "T2", lean := .tuple tuple2 }, { fift := "K2", lean := .cont (.quit 2) }, mkIntArg (-17)],
      #[{ fift := "C3", lean := .cell cell3 }, { fift := "S3", lean := .slice slice3 }, { fift := "B3", lean := .builder builder3 }],
      #[{ fift := "C4", lean := .cell cell4 }, { fift := "S4", lean := .slice slice4 }, { fift := "B4", lean := .builder builder4 }],
      #[cellBocArg1, sliceBocArg1, { fift := "T3", lean := .tuple tuple3 }],
      #[cellBocArg2, sliceBocArg2, { fift := "T4", lean := .tuple tuple4 }, { fift := "K4", lean := .cont (.quit 4) }],
      #[mkIntArg ((Int.ofNat (1 <<< 256)) - 1), mkIntArg (-(Int.ofNat (1 <<< 256))), mkIntArg 0],
      #[mkIntArg 9223372036854775807, mkIntArg (-9223372036854775808), { fift := "K3", lean := .cont (.quit 3) }]
    ]
  let randomCases := Nat.min randomCases (max * 32 + 1024)
  let randoms : Array (Array InitArg) :=
    Id.run do
      let mut rng : Rng64 := { state := mixSeed seed "no-input" }
      let mut out : Array (Array InitArg) := #[]
      for _ in [0:randomCases] do
        let (st, rng') := randStack rng 0 192
        out := out.push st
        rng := rng'
      out
  let merged := interleaveArrays base randoms
  (stackDedup merged).take max

def manualVariantsForRow (rowName : String) : Array (Array InitArg) :=
  match rowName with
  | "BLESS" | "BLESS_" =>
      #[
        #[{ fift := "S", lean := .slice emptySlice }],
        #[sliceBocArg1],
        #[sliceBocArg2],
        #[malformedDictSliceArg1],
        #[mkIntArg 1, sliceBocArg1],
        #[{ fift := "C1", lean := .cell cell1 }, mkIntArg (-7), sliceBocArg2]
      ]
  | "BLESSARGS" | "BLESSARGS_" =>
      #[
        #[sliceBocArg1],
        #[mkIntArg 1, sliceBocArg1],
        #[mkIntArg 1, mkIntArg 2, sliceBocArg2],
        #[{ fift := "C1", lean := .cell cell1 }, mkIntArg 7, sliceBocArg1],
        #[{ fift := "T1", lean := .tuple tuple1 }, { fift := "K1", lean := .cont (.quit 1) }, sliceBocArg2],
        #[malformedDictSliceArg2]
      ]
  | "BLESSVARARGS" | "BLESSVARARGS_" =>
      #[
        #[sliceBocArg1, mkIntArg 0, mkIntArg 0],
        #[sliceBocArg1, mkIntArg 1, mkIntArg 0],
        #[mkIntArg 11, sliceBocArg1, mkIntArg 1, mkIntArg 1],
        #[mkIntArg 11, mkIntArg 22, sliceBocArg2, mkIntArg 2, mkIntArg 0],
        #[mkIntArg 11, sliceBocArg2, mkIntArg 2, mkIntArg 1], -- pfx depth < r
        #[sliceBocArg2, mkIntArg (-1), mkIntArg 0],
        #[sliceBocArg2, mkIntArg 0, mkIntArg (-1)],
        #[malformedDictSliceArg1, mkIntArg 3, mkIntArg 2]
      ]
  | "CALLCCVARARGS" | "CALLXVARARGS" | "JMPXVARARGS" =>
      #[
        #[{ fift := "K1", lean := .cont (.quit 1) }, mkIntArg 0, mkIntArg 0],
        #[mkIntArg 7, { fift := "K1", lean := .cont (.quit 1) }, mkIntArg 1, mkIntArg 0],
        #[mkIntArg 7, mkIntArg 8, { fift := "K2", lean := .cont (.quit 2) }, mkIntArg 2, mkIntArg 0],
        #[mkIntArg 7, { fift := "K3", lean := .cont (.quit 3) }, mkIntArg 2, mkIntArg 0], -- p depth < p
        #[{ fift := "K4", lean := .cont (.quit 4) }, mkIntArg (-1), mkIntArg 0],
        #[{ fift := "K1", lean := .cont (.quit 1) }, mkIntArg 0, mkIntArg (-1)],
        #[{ fift := "T1", lean := .tuple tuple1 }, mkIntArg 3, { fift := "K2", lean := .cont (.quit 2) }, mkIntArg 1, mkIntArg 2],
        #[mkIntArg 1, mkIntArg 2, mkIntArg 3, { fift := "K1", lean := .cont (.quit 1) }, mkIntArg 3, mkIntArg 3]
      ]
  | "CALLXARGS" | "CALLXARGS_1" =>
      #[
        #[{ fift := "K1", lean := .cont (.quit 1) }],
        #[mkIntArg 7, { fift := "K1", lean := .cont (.quit 1) }],
        #[mkIntArg 7, mkIntArg 8, { fift := "K2", lean := .cont (.quit 2) }],
        #[{ fift := "C1", lean := .cell cell1 }, mkIntArg 9, { fift := "K3", lean := .cont (.quit 3) }]
      ]
  | "SETCONTVARARGS" =>
      #[
        #[{ fift := "K1", lean := .cont (.quit 1) }, mkIntArg 0, mkIntArg 0],
        #[mkIntArg 7, { fift := "K1", lean := .cont (.quit 1) }, mkIntArg 1, mkIntArg 0],
        #[mkIntArg 7, mkIntArg 8, { fift := "K2", lean := .cont (.quit 2) }, mkIntArg 2, mkIntArg 1],
        #[mkIntArg 7, { fift := "K3", lean := .cont (.quit 3) }, mkIntArg 2, mkIntArg 1], -- p depth < r
        #[{ fift := "K4", lean := .cont (.quit 4) }, mkIntArg (-1), mkIntArg 0],
        #[{ fift := "K4", lean := .cont (.quit 4) }, mkIntArg 0, mkIntArg (-1)],
        #[{ fift := "T1", lean := .tuple tuple1 }, mkIntArg 2, { fift := "K1", lean := .cont (.quit 1) }, mkIntArg 1, mkIntArg 3]
      ]
  | "SETNUMVARARGS" =>
      #[
        #[{ fift := "K", lean := .cont (.quit 0) }, mkIntArg 0],
        #[{ fift := "K1", lean := .cont (.quit 1) }, mkIntArg 1],
        #[{ fift := "K2", lean := .cont (.quit 2) }, mkIntArg 2],
        #[{ fift := "K3", lean := .cont (.quit 3) }, mkIntArg (-1)],
        #[{ fift := "K4", lean := .cont (.quit 4) }, mkIntArg 255],
        #[{ fift := "K1", lean := .cont (.quit 1) }, mkIntArg (Int.ofNat (1 <<< 255))]
      ]
  | "TRYARGS" =>
      #[
        #[{ fift := "K1", lean := .cont (.quit 1) }, { fift := "K2", lean := .cont (.quit 2) }],
        #[mkIntArg 7, { fift := "K1", lean := .cont (.quit 1) }, { fift := "K2", lean := .cont (.quit 2) }],
        #[mkIntArg 7, mkIntArg 8, { fift := "K3", lean := .cont (.quit 3) }, { fift := "K4", lean := .cont (.quit 4) }],
        #[{ fift := "C1", lean := .cell cell1 }, mkIntArg 9, { fift := "K1", lean := .cont (.quit 1) }, { fift := "K2", lean := .cont (.quit 2) }]
      ]
  | "DICTUGETJMPZ" | "DICTIGETJMPZ" | "DICTUGETEXECZ" | "DICTIGETEXECZ" =>
      #[
        #[mkIntArg 0, malformedDictCellArg1, mkIntArg 0],
        #[mkIntArg 1, malformedDictCellArg1, mkIntArg 1],
        #[mkIntArg (-1), malformedDictCellArg2, mkIntArg 2],
        #[mkIntArg ((Int.ofNat (1 <<< 255)) - 1), malformedDictCellArg1, mkIntArg 255],
        #[mkIntArg (-(Int.ofNat (1 <<< 255))), malformedDictCellArg2, mkIntArg 256],
        #[mkIntArg 7, { fift := "N", lean := .null }, mkIntArg 2],
        #[mkIntArg 7, cellBocArg1, mkIntArg 257],
        #[mkIntArg 7, cellBocArg2, mkIntArg (-1)]
      ]
  | "DICTUGETJMP" | "DICTIGETJMP" | "DICTUGETEXEC" | "DICTIGETEXEC" =>
      #[
        #[mkIntArg 0, malformedDictCellArg1, mkIntArg 0],
        #[mkIntArg 1, malformedDictCellArg1, mkIntArg 1],
        #[mkIntArg (-1), malformedDictCellArg2, mkIntArg 2],
        #[mkIntArg ((Int.ofNat (1 <<< 255)) - 1), malformedDictCellArg1, mkIntArg 255],
        #[mkIntArg (-(Int.ofNat (1 <<< 255))), malformedDictCellArg2, mkIntArg 256],
        #[mkIntArg 7, { fift := "N", lean := .null }, mkIntArg 2],
        #[mkIntArg 7, cellBocArg1, mkIntArg 257],
        #[mkIntArg 7, cellBocArg2, mkIntArg (-1)],
        #[mkIntArg 11, mkIntArg 22, malformedDictCellArg1, mkIntArg 3]
      ]
  | "DICTGETPREV" | "DICTGETPREVEQ" =>
      #[
        #[sliceBocArg1, malformedDictCellArg1, mkIntArg 0],
        #[sliceBocArg2, malformedDictCellArg2, mkIntArg 1],
        #[malformedDictSliceArg1, malformedDictCellArg1, mkIntArg 2],
        #[malformedDictSliceArg2, malformedDictCellArg2, mkIntArg 255],
        #[sliceBocArg1, { fift := "N", lean := .null }, mkIntArg 3],
        #[sliceBocArg2, cellBocArg1, mkIntArg 256],
        #[sliceBocArg1, cellBocArg2, mkIntArg (-1)]
      ]
  | "PFXDICTSET" | "PFXDICTREPLACE" | "PFXDICTADD" | "PFXDICTDEL" | "PFXDICTGETQ" | "PFXDICTGET"
    | "PFXDICTGETJMP" | "PFXDICTGETEXEC" | "PFXDICTSWITCH" =>
      #[
        #[sliceBocArg1, malformedDictCellArg1, mkIntArg 0],
        #[sliceBocArg2, malformedDictCellArg2, mkIntArg 1],
        #[malformedDictSliceArg1, malformedDictCellArg1, mkIntArg 2],
        #[malformedDictSliceArg2, malformedDictCellArg2, mkIntArg 255],
        #[sliceBocArg1, { fift := "N", lean := .null }, mkIntArg 3],
        #[sliceBocArg2, cellBocArg1, mkIntArg 256],
        #[sliceBocArg1, cellBocArg2, mkIntArg (-1)],
        #[mkIntArg 7, sliceBocArg1, malformedDictCellArg1, mkIntArg 4],
        #[mkIntArg 7, mkIntArg 8, sliceBocArg2, malformedDictCellArg2, mkIntArg 257],
        #[sliceBocArg1, malformedDictCellArg1, mkIntArg 8, sliceBocArg2]
      ]
  | "SUBDICTGET" | "SUBDICTIGET" | "SUBDICTUGET" | "SUBDICTRPGET" | "SUBDICTIRPGET" | "SUBDICTURPGET" =>
      #[
        #[sliceBocArg1, sliceBocArg2, malformedDictCellArg1, mkIntArg 4],
        #[sliceBocArg2, sliceBocArg1, malformedDictCellArg2, mkIntArg 4],
        #[malformedDictSliceArg1, sliceBocArg2, malformedDictCellArg1, mkIntArg 8],
        #[sliceBocArg1, malformedDictSliceArg2, malformedDictCellArg2, mkIntArg 16],
        #[malformedDictSliceArg1, malformedDictSliceArg2, malformedDictCellArg1, mkIntArg 255],
        #[sliceBocArg2, sliceBocArg1, { fift := "N", lean := .null }, mkIntArg 3],
        #[sliceBocArg1, sliceBocArg2, cellBocArg1, mkIntArg 256],
        #[sliceBocArg1, sliceBocArg2, cellBocArg2, mkIntArg (-1)],
        #[mkIntArg 7, sliceBocArg1, sliceBocArg2, malformedDictCellArg1, mkIntArg 2]
      ]
  | "SETCONTCTRMANY" =>
      #[
        #[{ fift := "K", lean := .cont (.quit 0) }],
        #[{ fift := "K1", lean := .cont (.quit 1) }],
        #[{ fift := "K2", lean := .cont (.quit 2) }],
        #[{ fift := "K3", lean := .cont (.quit 3) }],
        #[{ fift := "K4", lean := .cont (.quit 4) }],
        #[mkIntArg 7, { fift := "K1", lean := .cont (.quit 1) }],
        #[{ fift := "T1", lean := .tuple tuple1 }, { fift := "K2", lean := .cont (.quit 2) }]
      ]
  | "JMPXARGS" =>
      #[
        #[{ fift := "K1", lean := .cont (.quit 1) }],
        #[mkIntArg 1, { fift := "K1", lean := .cont (.quit 1) }],
        #[mkIntArg 1, mkIntArg 2, { fift := "K2", lean := .cont (.quit 2) }],
        #[mkIntArg 1, mkIntArg 2, mkIntArg 3, { fift := "K3", lean := .cont (.quit 3) }],
        #[{ fift := "C1", lean := .cell cell1 }, mkIntArg 9, { fift := "K4", lean := .cont (.quit 4) }]
      ]
  | "ENDC" | "ENDCST" =>
      #[
        #[{ fift := "B", lean := .builder emptyBuilder }],
        #[{ fift := "B1", lean := .builder builder1 }],
        #[{ fift := "B2", lean := .builder builder2 }],
        #[{ fift := "B3", lean := .builder builder3 }],
        #[{ fift := "B4", lean := .builder builder4 }],
        #[{ fift := "S1", lean := .slice slice1 }],
        #[mkIntArg 77, { fift := "B2", lean := .builder builder2 }],
        #[malformedDictSliceArg1, { fift := "B3", lean := .builder builder3 }]
      ]
  | "CDATASIZE" | "CDATASIZEQ" =>
      #[
        #[cellBocArg1, mkIntArg 0],
        #[cellBocArg1, mkIntArg 1],
        #[cellBocArg2, mkIntArg 2],
        #[malformedDictCellArg1, mkIntArg 3],
        #[malformedDictCellArg2, mkIntArg 255],
        #[cellBocArg1, mkIntArg 256],
        #[cellBocArg2, mkIntArg (-1)],
        #[{ fift := "N", lean := .null }, mkIntArg 0],
        #[mkIntArg 7, cellBocArg1, mkIntArg 2]
      ]
  | "STOPTSTDADDRQ" =>
      #[
        #[sliceBocArg1],
        #[sliceBocArg2],
        #[malformedDictSliceArg1],
        #[malformedDictSliceArg2],
        #[{ fift := "C1", lean := .cell cell1 }],
        #[mkIntArg 1, sliceBocArg2],
        #[mkIntArg (-1), malformedDictSliceArg1]
      ]
  | "SETGLOB" =>
      #[
        #[mkIntArg 0, mkIntArg 1],
        #[mkIntArg 1, mkIntArg (-1)],
        #[mkIntArg 7, { fift := "N", lean := .null }],
        #[mkIntArg 8, cellBocArg1],
        #[mkIntArg (-1), sliceBocArg1],
        #[mkIntArg 255, { fift := "T1", lean := .tuple tuple1 }],
        #[mkIntArg ((Int.ofNat (1 <<< 255)) - 1), { fift := "K1", lean := .cont (.quit 1) }]
      ]
  | "SETGLOBVAR" =>
      #[
        #[mkIntArg 0],
        #[mkIntArg 1],
        #[mkIntArg (-1)],
        #[{ fift := "N", lean := .null }],
        #[cellBocArg1],
        #[sliceBocArg1],
        #[{ fift := "T1", lean := .tuple tuple1 }],
        #[mkIntArg 7, mkIntArg 8]
      ]
  | "GETPARAMLONG" | "GETPARAMLONG2" =>
      #[
        #[],
        #[mkIntArg 0],
        #[mkIntArg 1, mkIntArg 2],
        #[cellBocArg1, sliceBocArg1, mkIntArg 3],
        #[malformedDictCellArg1, malformedDictSliceArg1],
        #[mkIntArg ((Int.ofNat (1 <<< 255)) - 1)],
        #[mkIntArg (-(Int.ofNat (1 <<< 255)))]
      ]
  | "PUSHINT_LONG" =>
      #[
        #[],
        #[mkIntArg 0],
        #[mkIntArg 1, mkIntArg 2],
        #[{ fift := "C1", lean := .cell cell1 }, { fift := "S1", lean := .slice slice1 }],
        mkStackMixed 12,
        mkStackTypedCycle 24,
        mkStackHetero 24
      ]
  | "RETARGS" =>
      #[
        #[],
        #[mkIntArg 1],
        #[mkIntArg 1, mkIntArg 2],
        #[mkIntArg 1, mkIntArg 2, mkIntArg 3],
        #[mkIntArg 1, mkIntArg 2, mkIntArg 3, mkIntArg 4],
        #[{ fift := "C1", lean := .cell cell1 }, mkIntArg 9]
      ]
  | "RETURNARGS" =>
      #[
        #[],
        #[mkIntArg 1],
        #[mkIntArg 1, mkIntArg 2],
        #[{ fift := "K1", lean := .cont (.quit 1) }, mkIntArg 3]
      ]
  | "THROWARG" =>
      #[
        #[mkIntArg 0],
        #[mkIntArg 1],
        #[mkIntArg (-1)],
        #[mkIntArg ((Int.ofNat (1 <<< 255)) - 1)],
        #[mkIntArg (-(Int.ofNat (1 <<< 255)))]
      ]
  | "THROWARGIF" | "THROWARGIFNOT" =>
      #[
        #[mkIntArg 0, mkIntArg 0],
        #[mkIntArg 1, mkIntArg 0],
        #[mkIntArg 1, mkIntArg 1],
        #[mkIntArg 1, mkIntArg (-1)],
        #[mkIntArg (-1), mkIntArg 1],
        #[mkIntArg ((Int.ofNat (1 <<< 255)) - 1), mkIntArg 1],
        #[mkIntArg (-(Int.ofNat (1 <<< 255))), mkIntArg 0]
      ]
  | "DICTMIN" | "DICTUMIN" | "DICTREMMAX" | "DICTUREMMINREF" =>
      #[
        #[malformedDictCellArg1, mkIntArg 2],
        #[malformedDictCellArg1, mkIntArg 3],
        #[malformedDictCellArg2, mkIntArg 2],
        #[mkIntArg 5, malformedDictCellArg1, mkIntArg 2],
        #[mkIntArg (-1), malformedDictCellArg2, mkIntArg 257]
      ]
  | "DICTUGETNEXTEQ" =>
      #[
        #[mkIntArg (-1), malformedDictCellArg1, mkIntArg 2],
        #[mkIntArg 1, malformedDictCellArg1, mkIntArg 2],
        #[mkIntArg 0, malformedDictCellArg2, mkIntArg 2]
      ]
  | "DICTREPLACEGETB" =>
      #[
        #[{ fift := "B2", lean := .builder builder2 }, malformedDictSliceArg1, malformedDictCellArg1, mkIntArg 3],
        #[{ fift := "B1", lean := .builder builder1 }, malformedDictSliceArg2, malformedDictCellArg2, mkIntArg 2],
        #[{ fift := "B4", lean := .builder builder4 }, malformedDictSliceArg1, malformedDictCellArg2, mkIntArg 257]
      ]
  | "SDCUTFIRST" =>
      #[
        #[malformedDictSliceArg1, mkIntArg 1],
        #[sliceBocArg2, mkIntArg 2],
        #[sliceBocArg2, mkIntArg 0]
      ]
  | "SDCUTLAST" =>
      #[
        #[malformedDictSliceArg1, mkIntArg 1],
        #[sliceBocArg2, mkIntArg 2],
        #[sliceBocArg2, mkIntArg 0]
      ]
  | "SDSUBSTR" =>
      #[
        #[malformedDictSliceArg1, mkIntArg 0, mkIntArg 1],
        #[malformedDictSliceArg1, mkIntArg 1, mkIntArg 1],
        #[sliceBocArg2, mkIntArg 0, mkIntArg 2],
        #[malformedDictSliceArg2, mkIntArg 0, mkIntArg 0],
        #[malformedDictSliceArg2, mkIntArg 2, mkIntArg 1]
      ]
  | _ =>
      #[]

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

def hasSubstr (s pat : String) : Bool :=
  (s.splitOn pat).length > 1

def anchorIdxs (n : Nat) : Array Nat :=
  if n == 0 then
    #[]
  else
    let raw : Array Nat := #[0, 1, 2, n / 3, n / 2, (2 * n) / 3, n - 3, n - 2, n - 1]
    Id.run do
      let mut out : Array Nat := #[]
      for i in raw do
        if i < n && !(out.contains i) then
          out := out.push i
      out

def idxsByType (inputs : Array (String × String)) (ty : String) : Array Nat :=
  Id.run do
    let mut out : Array Nat := #[]
    for i in [0:inputs.size] do
      if inputs[i]!.snd == ty then
        out := out.push i
    out

def idxsByAnyOrType (inputs : Array (String × String)) (ty : String) : Array Nat :=
  Id.run do
    let mut out : Array Nat := #[]
    for i in [0:inputs.size] do
      let t := inputs[i]!.snd
      if t == ty || t == "Any" then
        out := out.push i
    out

def buildVariants (rowName : String) (inputs : List (String × String)) (max : Nat) (randomCases : Nat := 0)
    (seed : UInt64 := 1) : IO (Array (Array InitArg)) := do
  let max := Nat.max 1 max
  if inputs.isEmpty then
    return buildNoInputStacks max randomCases seed

  let inputArr : Array (String × String) := inputs.toArray
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

  -- Full-vector sweeps: vary many args simultaneously to expose higher-order interactions.
  for k in [1:Nat.min 8 maxAlt] do
    let mut st := baseArgs
    let mut changed := false
    for i in [0:varsPerArg.size] do
      let vs := varsPerArg[i]!.snd
      if vs.size > k then
        st := st.set! i vs[k]!
        changed := true
      else if vs.size > 1 then
        let idx := k % vs.size
        st := st.set! i vs[idx]!
        if idx != 0 then
          changed := true
    if changed then
      core := core.push st

  -- Deterministic anchor combinations: covers cross-extremes and non-symmetric pairs.
  let argAnchors : Array (Array Nat) :=
    Array.ofFn (n := varsPerArg.size) fun i =>
      let vs := varsPerArg[i.1]!.snd
      anchorIdxs vs.size

  for i in [0:varsPerArg.size] do
    let vsi := varsPerArg[i]!.snd
    let anchors := argAnchors[i]!
    for ai in anchors do
      if vsi.size > ai then
        core := core.push (baseArgs.set! i vsi[ai]!)

  if varsPerArg.size ≥ 2 then
    for i in [0:varsPerArg.size] do
      for j in [i+1:varsPerArg.size] do
        let vsi := varsPerArg[i]!.snd
        let vsj := varsPerArg[j]!.snd
        let ai := (argAnchors[i]!).take 4
        let aj := (argAnchors[j]!).take 4
        for ii in ai do
          for jj in aj do
            if vsi.size > ii && vsj.size > jj then
              let st := (baseArgs.set! i vsi[ii]!).set! j vsj[jj]!
              core := core.push st

  -- Limited 3-arg anchor combinations for non-linear interaction coverage.
  if varsPerArg.size ≥ 3 then
    let n3 : Nat := Nat.min varsPerArg.size 5
    for i in [0:n3] do
      for j in [i+1:n3] do
        for k in [j+1:n3] do
          let vsi := varsPerArg[i]!.snd
          let vsj := varsPerArg[j]!.snd
          let vsk := varsPerArg[k]!.snd
          let ai := (argAnchors[i]!).take 2
          let aj := (argAnchors[j]!).take 2
          let ak := (argAnchors[k]!).take 2
          for ii in ai do
            for jj in aj do
              for kk in ak do
                if vsi.size > ii && vsj.size > jj && vsk.size > kk then
                  let st := ((baseArgs.set! i vsi[ii]!).set! j vsj[jj]!).set! k vsk[kk]!
                  core := core.push st

  -- Exhaustive typed cross-product for compact signatures.
  let exhaustiveCap : Nat := Nat.min 4096 (max * 8 + 256)
  if varsPerArg.size > 0 && varsPerArg.size ≤ 5 && exhaustiveCap > 0 then
    let mut doms : Array (Array InitArg) := #[]
    let mut canExhaustive := true
    let mut prod : Nat := 1
    for i in [0:varsPerArg.size] do
      let vsRaw := varsPerArg[i]!.snd
      let vs := if vsRaw.size ≤ 10 then vsRaw else vsRaw.take 10
      if vs.isEmpty then
        canExhaustive := false
      else if canExhaustive then
        let newProd := prod * vs.size
        if newProd > exhaustiveCap then
          canExhaustive := false
        else
          prod := newProd
      doms := doms.push vs
    if canExhaustive && prod > 0 then
      let mut idxs : Array Nat := Array.replicate varsPerArg.size 0
      let mut done := false
      let mut emitted : Nat := 0
      while !done && emitted < exhaustiveCap do
        let mut st := baseArgs
        for i in [0:varsPerArg.size] do
          let v := (doms[i]!)[idxs[i]!]!
          st := st.set! i v
        core := core.push st
        emitted := emitted + 1

        let mut pos := varsPerArg.size
        let mut advanced := false
        while !advanced do
          if pos == 0 then
            done := true
            advanced := true
          else
            let pos' := pos - 1
            let cur := idxs[pos']!
            let lim := (doms[pos']!).size
            if cur + 1 < lim then
              idxs := idxs.set! pos' (cur + 1)
              for t in [pos'+1:varsPerArg.size] do
                idxs := idxs.set! t 0
              advanced := true
            else
              pos := pos'

  let intIdxs : Array Nat :=
    Id.run do
      let mut out : Array Nat := #[]
      for i in [0:inputArr.size] do
        let ty := inputArr[i]!.snd
        if ty == "Int" then
          out := out.push i
      out
  if intIdxs.size > 0 then
    let minInt257 : Int := -(Int.ofNat (1 <<< 256))
    let maxInt257 : Int := (Int.ofNat (1 <<< 256)) - 1
    let pushIntIfFresh (xs : Array Int) (v : Int) : Array Int :=
      if xs.contains v then xs else xs.push v
    let intScenarios : Array Int :=
      #[
        0, 1, -1, 2, -2, 3, -3, 7, -7, 8, -8, 15, -15, 16, -16,
        31, -31, 32, -32, 63, -63, 64, -64, 127, -127, 128, -128,
        254, 255, 256, 257, 511, 512, 1022, 1023, 1024, -255, -256, -257, -511, -512, -1024,
        Int.ofNat (1 <<< 255), -(Int.ofNat (1 <<< 255)),
        maxInt257, maxInt257 - 1, minInt257 + 1, minInt257
      ]
    for v in intScenarios do
      let mut st := baseArgs
      for idx in intIdxs do
        st := st.set! idx (mkIntArg v)
      core := core.push st
    if intIdxs.size ≥ 2 then
      let mut altHiLo := baseArgs
      let mut altLoHi := baseArgs
      for k in [0:intIdxs.size] do
        let idx := intIdxs[k]!
        let vA := if k % 2 == 0 then maxInt257 else minInt257
        let vB := if k % 2 == 0 then minInt257 else maxInt257
        altHiLo := altHiLo.set! idx (mkIntArg vA)
        altLoHi := altLoHi.set! idx (mkIntArg vB)
      core := core.push altHiLo
      core := core.push altLoHi
      -- Two-int targeted pairs (for arithmetic/compare/div/mod semantics).
      let intPairs : Array (Int × Int) :=
        #[
          (0, 0),
          (1, 1),
          (1, -1),
          (-1, 1),
          (2, -2),
          (-2, 2),
          (255, 1),
          (1, 255),
          (maxInt257, 1),
          (1, maxInt257),
          (minInt257, 1),
          (1, minInt257),
          (maxInt257, minInt257),
          (minInt257, maxInt257)
        ]
      let a0 := intIdxs[0]!
      let a1 := intIdxs[1]!
      for (x, y) in intPairs do
        let st := (baseArgs.set! a0 (mkIntArg x)).set! a1 (mkIntArg y)
        core := core.push st
      if intIdxs.size ≥ 3 then
        let a2 := intIdxs[2]!
        let triads : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (1, -1, 1),
            (maxInt257, minInt257, 1),
            (maxInt257, 1, minInt257),
            (minInt257, maxInt257, -1)
          ]
        for (x, y, z) in triads do
          let st := ((baseArgs.set! a0 (mkIntArg x)).set! a1 (mkIntArg y)).set! a2 (mkIntArg z)
          core := core.push st
    let isDivLike := hasSubstr rowName "DIV" || hasSubstr rowName "MOD" || hasSubstr rowName "SHIFT"
    if isDivLike then
      let targetIdx := intIdxs[intIdxs.size - 1]!
      let denomVals : Array Int := #[0, 1, -1, 2, -2, 255, -255, maxInt257, minInt257]
      for dv in denomVals do
        let mut st := baseArgs
        for idx in intIdxs do
          if idx == targetIdx then
            st := st.set! idx (mkIntArg dv)
          else
            st := st.set! idx (mkIntArg 1)
        core := core.push st
    let isDictLike := hasSubstr rowName "DICT"
    if isDictLike then
      let lenIdx := intIdxs[intIdxs.size - 1]!
      let lenScenarios : Array Int :=
        #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257, 511, 512, 1022, 1023]
      for lv in lenScenarios do
        let mut st := baseArgs
        for idx in intIdxs do
          if idx == lenIdx then
            st := st.set! idx (mkIntArg lv)
          else
            st := st.set! idx (mkIntArg 0)
        core := core.push st
      if intIdxs.size ≥ 2 then
        let keyIdx := intIdxs[0]!
        let keyScenarios : Array Int := #[0, 1, -1, 2, -2, 255, -255, maxInt257, minInt257]
        for kv in keyScenarios do
          for lv in lenScenarios.take 9 do
            let st := (baseArgs.set! keyIdx (mkIntArg kv)).set! lenIdx (mkIntArg lv)
            core := core.push st

    -- Size-derived boundaries for slice/cell/builder + int signatures.
    let targetIntIdx := intIdxs[intIdxs.size - 1]!
    let sliceLikeIdxs := idxsByAnyOrType inputArr "Slice"
    if !sliceLikeIdxs.isEmpty then
      let si := sliceLikeIdxs[0]!
      let mut bounds : Array Int := #[-2, -1, 0, 1, 2, 3, 7, 8, 15, 16, 31, 32]
      for a in varsPerArg[si]!.snd do
        match a.lean with
        | .slice s =>
            let b : Int := Int.ofNat s.bitsRemaining
            let r : Int := Int.ofNat s.refsRemaining
            for v in #[b - 2, b - 1, b, b + 1, b + 2, r - 2, r - 1, r, r + 1, r + 2] do
              bounds := pushIntIfFresh bounds v
        | _ => pure ()
      for v in bounds.take 64 do
        let mut st := baseArgs
        for idx in intIdxs do
          st := st.set! idx (if idx == targetIntIdx then mkIntArg v else mkIntArg 0)
        core := core.push st

    let cellLikeIdxs2 := idxsByAnyOrType inputArr "Cell"
    if !cellLikeIdxs2.isEmpty then
      let ci := cellLikeIdxs2[0]!
      let mut bounds : Array Int := #[-2, -1, 0, 1, 2, 3, 4]
      for a in varsPerArg[ci]!.snd do
        match a.lean with
        | .cell c =>
            let b : Int := Int.ofNat c.bits.size
            let r : Int := Int.ofNat c.refs.size
            for v in #[b - 2, b - 1, b, b + 1, b + 2, r - 2, r - 1, r, r + 1, r + 2] do
              bounds := pushIntIfFresh bounds v
        | _ => pure ()
      for v in bounds.take 64 do
        let mut st := baseArgs
        for idx in intIdxs do
          st := st.set! idx (if idx == targetIntIdx then mkIntArg v else mkIntArg 0)
        core := core.push st

    let builderLikeIdxs := idxsByAnyOrType inputArr "Builder"
    if !builderLikeIdxs.isEmpty then
      let bi := builderLikeIdxs[0]!
      let mut bounds : Array Int := #[-2, -1, 0, 1, 2, 3, 4]
      for a in varsPerArg[bi]!.snd do
        match a.lean with
        | .builder b =>
            let bitsN : Int := Int.ofNat b.bits.size
            let refsN : Int := Int.ofNat b.refs.size
            for v in #[bitsN - 2, bitsN - 1, bitsN, bitsN + 1, bitsN + 2, refsN - 2, refsN - 1, refsN, refsN + 1, refsN + 2] do
              bounds := pushIntIfFresh bounds v
        | _ => pure ()
      for v in bounds.take 64 do
        let mut st := baseArgs
        for idx in intIdxs do
          st := st.set! idx (if idx == targetIntIdx then mkIntArg v else mkIntArg 0)
        core := core.push st

    -- Vararg-shape cases: couple x_... prefix depth with p/r/n counters and near-miss offsets.
    let findNamedIntIdx? (want : String) : Option Nat :=
      Id.run do
        let mut out : Option Nat := none
        for i in [0:inputArr.size] do
          let (nm, ty) := inputArr[i]!
          if ty == "Int" && nm == want then
            out := some i
            break
        out
    let pIdx? := findNamedIntIdx? "p"
    let rIdx? := findNamedIntIdx? "r"
    let nIdx? := findNamedIntIdx? "n"
    if pIdx?.isSome || rIdx?.isSome || nIdx?.isSome then
      let prefixes : Array (Array InitArg) :=
        #[
          #[],
          #[mkIntArg 1],
          #[mkIntArg 1, mkIntArg 2],
          #[mkIntArg 1, mkIntArg 2, mkIntArg 3],
          #[{ fift := "C1", lean := .cell cell1 }],
          #[{ fift := "T1", lean := .tuple tuple1 }],
          #[mkIntArg 7, { fift := "K1", lean := .cont (.quit 1) }],
          #[mkIntArg 7, mkIntArg 8, { fift := "S1", lean := .slice slice1 }]
        ]
      for pfx in prefixes do
        let d : Int := Int.ofNat pfx.size
        let near : Array Int := #[d - 1, d, d + 1, 0, 1, 2, -1, 255, -255]

        -- Fully matched counters.
        let mut matched := baseArgs
        match pIdx? with
        | some i => matched := matched.set! i (mkIntArg d)
        | none => pure ()
        match rIdx? with
        | some i => matched := matched.set! i (mkIntArg d)
        | none => pure ()
        match nIdx? with
        | some i => matched := matched.set! i (mkIntArg d)
        | none => pure ()
        core := core.push (pfx ++ matched)

        -- Near-miss single-counter perturbations.
        for v in near do
          match pIdx? with
          | some i => core := core.push (pfx ++ (matched.set! i (mkIntArg v)))
          | none => pure ()
          match rIdx? with
          | some i => core := core.push (pfx ++ (matched.set! i (mkIntArg v)))
          | none => pure ()
          match nIdx? with
          | some i => core := core.push (pfx ++ (matched.set! i (mkIntArg v)))
          | none => pure ()

        -- Joint p/r couplings (important for call/jmp vararg semantics).
        match (pIdx?, rIdx?) with
        | (some pi, some ri) =>
            let combos : Array (Int × Int) :=
              #[
                (d, d),
                (d, 0),
                (0, d),
                (d + 1, d),
                (d, d + 1),
                (d - 1, d),
                (d, d - 1),
                (-1, d),
                (d, -1),
                (255, 0),
                (0, 255)
              ]
            for (pv, rv) in combos do
              let st := (matched.set! pi (mkIntArg pv)).set! ri (mkIntArg rv)
              core := core.push (pfx ++ st)
        | _ => pure ()

  -- Structured malformed typed values (still type-correct at signature level).
  let cellLikeIdxs := idxsByAnyOrType inputArr "Cell"
  let sliceLikeIdxs := idxsByAnyOrType inputArr "Slice"
  for idx in cellLikeIdxs do
    core := core.push (baseArgs.set! idx malformedDictCellArg1)
    core := core.push (baseArgs.set! idx malformedDictCellArg2)
    core := core.push (baseArgs.set! idx cellBocArg1)
    core := core.push (baseArgs.set! idx cellBocArg2)
  for idx in sliceLikeIdxs do
    core := core.push (baseArgs.set! idx malformedDictSliceArg1)
    core := core.push (baseArgs.set! idx malformedDictSliceArg2)
    core := core.push (baseArgs.set! idx sliceBocArg1)
    core := core.push (baseArgs.set! idx sliceBocArg2)
  if !cellLikeIdxs.isEmpty && !sliceLikeIdxs.isEmpty then
    let ci := cellLikeIdxs[0]!
    let si := sliceLikeIdxs[0]!
    core := core.push ((baseArgs.set! ci malformedDictCellArg1).set! si malformedDictSliceArg1)
    core := core.push ((baseArgs.set! ci malformedDictCellArg2).set! si malformedDictSliceArg2)
    core := core.push ((baseArgs.set! ci cellBocArg1).set! si sliceBocArg2)
  if !cellLikeIdxs.isEmpty && intIdxs.size > 0 then
    let ci := cellLikeIdxs[0]!
    let ki := intIdxs[intIdxs.size - 1]!
    let st1 := (baseArgs.set! ci malformedDictCellArg1).set! ki (mkIntArg 2)
    let st2 := (baseArgs.set! ci malformedDictCellArg2).set! ki (mkIntArg 257)
    core := core.push st1
    core := core.push st2

  core := stackDedup core

  let nArgs := varsPerArg.size
  let wantUnderflow : Nat := if nArgs > 0 then 2 else 0
  let wantWrong : Nat :=
    Nat.min 8 <| varsPerArg.foldl (init := 0) fun acc (ty, _vs) => acc + (if (wrongTypeFor ty).isSome then 2 else 0)
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

  -- Two-arg wrong-type combinations.
  if out.size < wantValid + wantWrong && varsPerArg.size ≥ 2 then
    for i in [0:varsPerArg.size] do
      if out.size >= wantValid + wantWrong then
        break
      for j in [i+1:varsPerArg.size] do
        if out.size >= wantValid + wantWrong then
          break
        let tyi := varsPerArg[i]!.fst
        let tyj := varsPerArg[j]!.fst
        match (wrongTypeFor tyi, wrongTypeFor tyj) with
        | (some bi, some bj) =>
            let st := (baseArgs.set! i bi).set! j bj
            if !(out.any (fun st' => stackKey st' == stackKey st)) then
              out := out.push st
        | _ =>
            pure ()

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

  -- If still short, synthesize additional deterministic deep-stack variants by
  -- adding unique prefixes below the required input window (preserves top args).
  if out.size < max && core.size > 0 then
    let mut bump : Nat := 0
    let budget : Nat := max * 8 + 32
    while out.size < max && bump < budget do
      let base := core[bump % core.size]!
      let n1 : Int := Int.ofNat (1000 + bump)
      let n2 : Int := Int.ofNat (2000 + bump)
      let pfx : Array InitArg :=
        if bump % 3 == 0 then
          #[mkIntArg n1]
        else if bump % 3 == 1 then
          #[mkIntArg n1, { fift := "C1", lean := .cell cell1 }]
        else
          #[mkIntArg n1, mkIntArg n2]
      let st := pfx ++ base
      out := pushIfFresh out st
      bump := bump + 1

  let randomCases := Nat.min randomCases (max * 32 + 1024)
  let randoms : Array (Array InitArg) :=
    Id.run do
      let tag := rowName ++ "::" ++ String.intercalate "," (inputs.map (fun (nm, ty) => nm ++ ":" ++ ty))
      let mut rng : Rng64 := { state := mixSeed seed ("sig:" ++ tag) }
      let mut outR : Array (Array InitArg) := #[]
      let wrongChoices : Array (Nat × InitArg) :=
        Id.run do
          let mut w : Array (Nat × InitArg) := #[]
          for i in [0:varsPerArg.size] do
            let ty := varsPerArg[i]!.fst
            match wrongTypeFor ty with
            | some bad => w := w.push (i, bad)
            | none => pure ()
          w
      let malformedChoices : Array (Nat × InitArg) :=
        Id.run do
          let mut m : Array (Nat × InitArg) := #[]
          for i in [0:inputArr.size] do
            let ty := inputArr[i]!.snd
            if ty == "Cell" || ty == "Any" then
              m := m.push (i, malformedDictCellArg1)
              m := m.push (i, malformedDictCellArg2)
            if ty == "Slice" || ty == "Any" then
              m := m.push (i, malformedDictSliceArg1)
              m := m.push (i, malformedDictSliceArg2)
          m
      for _ in [0:randomCases] do
        let (pick, rng1) := rng.nextNat 18
        rng := rng1
        if pick < 9 then
          let (pickCore, rng2a) := rng.nextNat 4
          let (base, rng2) :=
            if pickCore == 0 then
              randTypedCoreAnchored varsPerArg rng2a
            else
              randTypedCore varsPerArg rng2a
          let (pfx, rng3) := randPrefix rng2
          outR := outR.push (pfx ++ base)
          rng := rng3
        else if pick < 11 then
          if wrongChoices.isEmpty then
            let (base, rng2) := randTypedCore varsPerArg rng
            let (pfx, rng3) := randPrefix rng2
            outR := outR.push (pfx ++ base)
            rng := rng3
          else
            let (wi, rng2) := rng.nextNat wrongChoices.size
            let (iBad, bad) := wrongChoices[wi]!
            let (base, rng3) := randTypedCore varsPerArg rng2
            let st := base.set! iBad bad
            let (pfx, rng4) := randPrefix rng3
            outR := outR.push (pfx ++ st)
            rng := rng4
        else if pick < 13 then
          if malformedChoices.isEmpty then
            let (base, rng2) := randTypedCore varsPerArg rng
            let (pfx, rng3) := randPrefix rng2
            outR := outR.push (pfx ++ base)
            rng := rng3
          else
            let (mi, rng2) := rng.nextNat malformedChoices.size
            let (iBad, bad) := malformedChoices[mi]!
            let (base, rng3) := randTypedCore varsPerArg rng2
            let st := base.set! iBad bad
            let (pfx, rng4) := randPrefix rng3
            outR := outR.push (pfx ++ st)
            rng := rng4
        else if pick < 15 then
          if wrongChoices.size < 2 then
            let (base, rng2) := randTypedCore varsPerArg rng
            let (pfx, rng3) := randPrefix rng2
            outR := outR.push (pfx ++ base)
            rng := rng3
          else
            let (w1, rng2) := rng.nextNat wrongChoices.size
            let (w2, rng3) := rng2.nextNat wrongChoices.size
            let (base, rng4) := randTypedCore varsPerArg rng3
            let (i1, b1) := wrongChoices[w1]!
            let (i2, b2) := wrongChoices[w2]!
            let st :=
              if i1 == i2 then
                base.set! i1 b1
              else
                (base.set! i1 b1).set! i2 b2
            let (pfx, rng5) := randPrefix rng4
            outR := outR.push (pfx ++ st)
            rng := rng5
        else if pick < 16 then
          if cellLikeIdxs.isEmpty || sliceLikeIdxs.isEmpty then
            let (base, rng2) := randTypedCore varsPerArg rng
            let (pfx, rng3) := randPrefix rng2
            outR := outR.push (pfx ++ base)
            rng := rng3
          else
            let (base, rng2) := randTypedCore varsPerArg rng
            let (ci, rng3) := rng2.nextNat cellLikeIdxs.size
            let (si, rng4) := rng3.nextNat sliceLikeIdxs.size
            let (cb, rng5) := rng4.nextNat 2
            let (sb, rng6) := rng5.nextNat 2
            let cBad := if cb == 0 then malformedDictCellArg1 else malformedDictCellArg2
            let sBad := if sb == 0 then malformedDictSliceArg1 else malformedDictSliceArg2
            let st := (base.set! cellLikeIdxs[ci]! cBad).set! sliceLikeIdxs[si]! sBad
            let (pfx, rng7) := randPrefix rng6
            outR := outR.push (pfx ++ st)
            rng := rng7
        else if pick < 17 then
          if intIdxs.isEmpty then
            let (base, rng2) := randTypedCore varsPerArg rng
            let (pfx, rng3) := randPrefix rng2
            outR := outR.push (pfx ++ base)
            rng := rng3
          else
            let (base, rng2) := randTypedCore varsPerArg rng
            let (ii, rng3) := rng2.nextNat intIdxs.size
            let tweakVals : Array Int := #[0, 1, -1, 255, 256, 257, 1023, -1024, (Int.ofNat (1 <<< 255)), -(Int.ofNat (1 <<< 255))]
            let (tv, rng4) := rng3.nextNat tweakVals.size
            let st := base.set! intIdxs[ii]! (mkIntArg tweakVals[tv]!)
            let (pfx, rng5) := randPrefix rng4
            outR := outR.push (pfx ++ st)
            rng := rng5
        else
          if nArgs == 0 then
            outR := outR.push #[]
          else
            let (k, rng2) := rng.nextNat nArgs
            let st := baseArgs.take k
            outR := outR.push st
            rng := rng2
      outR

  let merged := interleaveArrays out randoms
  pure ((stackDedup merged).take max)

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
    (casesPerInstr? : Option Nat := none) (verbose : Bool := false) (maxNoSigDepth : Nat := 64)
    (minCasesPerInstr : Nat := 10) (randomCasesPerInstr : Nat := 0) (seed : UInt64 := 1) : IO Unit := do
  let rowSeed := mixSeed seed row.name
  let codePairs0 ←
    match buildCodeCells row maxCodeVariantsPerInstr randomCasesPerInstr rowSeed with
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

  if row.name == "RUNVMX" then
    -- Deterministic + random mode-aware RUNVMX stacks.
    let mkProg (bits : Array BitString) : IO (Cell × String) := do
      let allBits := bits.foldl (init := #[]) fun acc b => acc ++ b
      let cell := Cell.mkOrdinary allBits #[]
      let bocBytes ←
        match stdBocSerialize cell with
        | .ok b => pure b
        | .error e => die s!"RUNVMX: stdBocSerialize failed: {reprStr e}"
      let hex := bytesToHex bocBytes
      pure (cell, hex)

    let retBits ←
      match encodeCp0 .ret with
      | .ok b => pure b
      | .error e => die s!"RUNVMX: encodeCp0 RET failed: {reprStr e}"
    let push7Bits ←
      match encodeCp0 (.pushInt (.num 7)) with
      | .ok b => pure b
      | .error e => die s!"RUNVMX: encodeCp0 PUSHINT 7 failed: {reprStr e}"

    let (progRetCell, progRetHex) ← mkProg #[retBits]
    let (progPush7RetCell, progPush7RetHex) ← mkProg #[push7Bits, retBits]

    let mkSliceArg (cell : Cell) (hex : String) : InitArg :=
      { fift := s!"SB:{hex}", lean := .slice (Slice.ofCell cell) }

    let progRet := mkSliceArg progRetCell progRetHex
    let progPush7Ret := mkSliceArg progPush7RetCell progPush7RetHex
    let progChoices : Array InitArg := #[progRet, progPush7Ret]

    let modeNeedsRetVals (mode : Nat) : Bool := (mode &&& 256) != 0
    let modeNeedsData (mode : Nat) : Bool := (mode &&& 4) != 0
    let modeNeedsC7 (mode : Nat) : Bool := (mode &&& 16) != 0
    let modeNeedsGasLimit (mode : Nat) : Bool := (mode &&& 8) != 0
    let modeNeedsGasMax (mode : Nat) : Bool := (mode &&& 64) != 0

    let mkPrefixForMode (stackItems : Array InitArg) (prog : InitArg) (mode : Nat) (retVals : Nat := 1) :
        Array InitArg :=
      Id.run do
        let mut p : Array InitArg := stackItems ++ #[mkIntArg (Int.ofNat stackItems.size), prog]
        if modeNeedsRetVals mode then
          p := p.push (mkIntArg (Int.ofNat retVals))
        if modeNeedsData mode then
          p := p.push { fift := "C1", lean := .cell cell1 }
        if modeNeedsC7 mode then
          p := p.push { fift := "T1", lean := .tuple tuple1 }
        if modeNeedsGasLimit mode then
          p := p.push (mkIntArg 1_000_000)
        if modeNeedsGasMax mode then
          p := p.push (mkIntArg 2_000_000)
        p

    let mkInitForMode (stackItems : Array InitArg) (prog : InitArg) (mode : Nat) (retVals : Nat := 1) :
        Array InitArg :=
      (mkPrefixForMode stackItems prog mode retVals) ++ #[mkIntArg (Int.ofNat mode)]

    let modes : Array Nat := #[0, 1, 2, 3, 4, 5, 8, 9, 16, 17, 32, 33, 64, 65, 128, 129, 256, 257, 510, 511]
    let stackSeeds : Array (Array InitArg) :=
      #[
        #[],
        #[mkIntArg 0],
        #[mkIntArg 1],
        #[mkIntArg (-1)],
        #[mkIntArg 1, mkIntArg 2],
        #[mkIntArg 1, mkIntArg 2, mkIntArg 3],
        #[{ fift := "C1", lean := .cell cell1 }],
        #[{ fift := "S1", lean := .slice slice1 }],
        #[{ fift := "B1", lean := .builder builder1 }],
        #[{ fift := "T1", lean := .tuple tuple1 }],
        mkIntStackAsc 4,
        mkIntStackDesc 4,
        mkStackMixed 4,
        mkIntStackAsc 8,
        mkStackMixed 8
      ]

    let code := codePairs[0]!.snd
    let casesWanted : Nat := (casesPerInstr?.getD 20) |> Nat.max 1
    let mut inits : Array (Array InitArg) := #[]

    let pushInitIfFresh (xs : Array (Array InitArg)) (st : Array InitArg) : Array (Array InitArg) :=
      if xs.any (fun st' => stackKey st' == stackKey st) then
        xs
      else
        xs.push st

    -- Deterministic mode/path coverage.
    for mode in modes do
      if inits.size >= casesWanted then
        break
      for st in stackSeeds do
        if inits.size >= casesWanted then
          break
        for p in progChoices do
          if inits.size >= casesWanted then
            break
          let rvChoices : Array Nat :=
            if modeNeedsRetVals mode then
              #[0, 1, 2, st.size, st.size + 1]
            else
              #[1]
          for rv in rvChoices do
            if inits.size >= casesWanted then
              break
            let init := mkInitForMode st p mode rv
            inits := pushInitIfFresh inits init

    -- Explicit malformed/underflow/invalid-flag cases.
    let explicit : Array (Array InitArg) :=
      #[
        #[mkIntArg (-1)],
        #[mkIntArg 512],
        #[mkIntArg 4095],
        #[mkIntArg 0],                      -- missing code/stacksize
        #[progRet, mkIntArg 0],             -- missing stacksize position (wrong order)
        #[mkIntArg 1, progRet, mkIntArg 0], -- stacksize too large for available args
        #[mkIntArg (-1), progRet, mkIntArg 0], -- negative stacksize
        #[mkIntArg 1, mkIntArg 511]         -- mode=511 with missing optional args
      ]
    for st in explicit do
      if inits.size >= casesWanted then
        break
      inits := pushInitIfFresh inits st

    -- Seeded random expansion (mode-aware).
    if inits.size < casesWanted then
      let mut rng : Rng64 := { state := mixSeed rowSeed "runvmx-cases" }
      let mut bump : Nat := 0
      let budget : Nat := casesWanted * 64 + 512
      while inits.size < casesWanted && bump < budget do
        let (mi, rng1) := rng.nextNat modes.size
        let mode := modes[mi]!
        let (pi, rng2) := rng1.nextNat progChoices.size
        let prog := progChoices[pi]!
        let (stRand, rng3) := randStack rng2 0 8
        let (rvRaw, rng4) := rng3.nextNat (stRand.size + 5)
        let rv := if modeNeedsRetVals mode then rvRaw else 1
        let (kind, rng5) := rng4.nextNat 5
        let init : Array InitArg :=
          if kind == 0 then
            mkInitForMode stRand prog mode rv
          else if kind == 1 then
            -- wrong order: put mode below required tail
            (mkPrefixForMode stRand prog mode rv) ++ #[mkIntArg 0]
          else if kind == 2 then
            -- short underflow-ish stack with only mode.
            #[mkIntArg (Int.ofNat mode)]
          else if kind == 3 then
            -- invalid flags.
            let badFlags : Array Int := #[-1, 512, 1023, 4095]
            let bi : Nat := rvRaw % badFlags.size
            #[mkIntArg badFlags[bi]!]
          else
            -- negative stack size in otherwise valid layout.
            let pfx := mkPrefixForMode stRand prog mode rv
            if pfx.size > 0 then
              let stackSizePos := stRand.size
              (pfx.set! stackSizePos (mkIntArg (-1))) ++ #[mkIntArg (Int.ofNat mode)]
            else
              mkInitForMode stRand prog mode rv
        inits := pushInitIfFresh inits init
        rng := rng5
        bump := bump + 1

    let cases : Array (Cell × Array InitArg) :=
      (inits.take casesWanted).map (fun st => (code, st))
    if cases.size < minCasesPerInstr then
      die s!"RUNVMX: generated only {cases.size} cases (< min {minCasesPerInstr}); increase --cases/--variants/--code-variants"

    let oracleInputs : Array (Cell × List String) :=
      cases.map (fun (c, init) => (c, init.toList.map (·.fift)))
    let oracleOuts ← runOracleBatch oracleInputs

    for cidx in [0:cases.size] do
      let (code, init) := cases[cidx]!
      if verbose then
        let argDump := String.intercalate " " (init.toList.map (·.fift))
        IO.println s!"RUNVMX (case {cidx+1}/{cases.size}): {argDump}"
      let initStack : Array Value := init.map (·.lean)
      let oracle ←
        match oracleOuts[cidx]? with
        | some o => pure o
        | none => die s!"RUNVMX (case {cidx+1}): missing oracle output"
      let leanRes := runLean code initStack
      let (leanExit, stF) ←
        match leanRes with
        | .halt ec st => pure (ec, st)
        | .continue _ => die "RUNVMX: Lean did not halt (fuel exhausted)"
      let exitRawLean : Int := ~~~ leanExit
      let gasUsedLean : Int := stF.gas.gasConsumed
      if exitRawLean != oracle.exitRaw then
        die s!"RUNVMX (case {cidx+1}): EXIT mismatch lean_raw={exitRawLean} oracle={oracle.exitRaw} (lean_exit={leanExit})"
      if gasUsedLean != oracle.gasUsed then
        die s!"RUNVMX (case {cidx+1}): GAS mismatch lean={gasUsedLean} oracle={oracle.gasUsed}"
      let (c4Out, c5Out) := leanOutCells stF
      let c4HashLean : String := hashHex (Cell.hashBytes c4Out)
      let c5HashLean : String := hashHex (Cell.hashBytes c5Out)
      if c4HashLean != oracle.c4Hash then
        die s!"RUNVMX (case {cidx+1}): C4 mismatch lean={c4HashLean} oracle={oracle.c4Hash}"
      if c5HashLean != oracle.c5Hash then
        die s!"RUNVMX (case {cidx+1}): C5 mismatch lean={c5HashLean} oracle={oracle.c5Hash}"
      let stackLeanTop : Array String :=
        Array.ofFn (n := stF.stack.size) fun i =>
          canonValue (stF.stack[stF.stack.size - 1 - i.1]!)
      if stackLeanTop.size != oracle.stackTop.size then
        die s!"RUNVMX (case {cidx+1}): DEPTH mismatch lean={stackLeanTop.size} oracle={oracle.stackTop.size}"
      for i in [0:stackLeanTop.size] do
        let a := stackLeanTop[i]!
        let b := oracle.stackTop[i]!
        if a != b then
          let leanDump := String.intercalate " | " stackLeanTop.toList
          let oracleDump := String.intercalate " | " oracle.stackTop.toList
          die s!"RUNVMX (case {cidx+1}): STACK mismatch at idx={i} lean='{a}' oracle='{b}'\nlean_stack_top={leanDump}\noracle_stack_top={oracleDump}"
    return ()

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

    let modeNeedsRetVals (mode : Nat) : Bool := (mode &&& 256) != 0
    let modeNeedsData (mode : Nat) : Bool := (mode &&& 4) != 0
    let modeNeedsC7 (mode : Nat) : Bool := (mode &&& 16) != 0
    let modeNeedsGasLimit (mode : Nat) : Bool := (mode &&& 8) != 0
    let modeNeedsGasMax (mode : Nat) : Bool := (mode &&& 64) != 0

    let mkInitForMode (stackItems : Array InitArg) (prog : InitArg) (mode : Nat) (retVals : Nat := 1) :
        Array InitArg :=
      Id.run do
        let mut p : Array InitArg := stackItems ++ #[mkIntArg (Int.ofNat stackItems.size), prog]
        if modeNeedsRetVals mode then
          p := p.push (mkIntArg (Int.ofNat retVals))
        if modeNeedsData mode then
          p := p.push { fift := "C1", lean := .cell cell1 }
        if modeNeedsC7 mode then
          p := p.push { fift := "T1", lean := .tuple tuple1 }
        if modeNeedsGasLimit mode then
          p := p.push (mkIntArg 1_000_000)
        if modeNeedsGasMax mode then
          p := p.push (mkIntArg 2_000_000)
        p

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

    -- Additional deterministic mode coverage beyond {0,1,510,511}.
    let extraModes : Array Nat := #[2, 3, 4, 5, 8, 9, 16, 17, 32, 33, 64, 65, 128, 129, 256, 257]
    for mode in extraModes do
      if cases.size >= casesWanted then
        break
      match findCode? mode with
      | none => pure ()
      | some codeM =>
          cases := cases ++ #[
            (mode, codeM, mkInitForMode #[] progRet mode 1),
            (mode, codeM, mkInitForMode #[] progPush7Ret mode 1),
            (mode, codeM, mkInitForMode #[mkIntArg 5] progRet mode 1),
            (mode, codeM, mkInitForMode #[mkIntArg 1, mkIntArg 2] progPush7Ret mode 2)
          ]

    -- Include invalid immediate modes if present in generated code variants.
    for (m, codeM) in codePairs do
      if cases.size >= casesWanted then
        break
      if m ≥ 512 then
        cases := cases ++ #[
          (m, codeM, #[]),
          (m, codeM, #[mkIntArg 1, progRet])
        ]

    let caseExists (mode : Nat) (init : Array InitArg) : Bool :=
      cases.any (fun (m, _c, st) => m == mode && stackKey st == stackKey init)

    let stackSeeds : Array (Array InitArg) :=
      #[
        #[],
        #[mkIntArg 0],
        #[mkIntArg 1],
        #[mkIntArg (-1)],
        #[mkIntArg 1, mkIntArg 2],
        #[mkIntArg 1, mkIntArg 2, mkIntArg 3],
        #[{ fift := "C1", lean := .cell cell1 }],
        #[{ fift := "S1", lean := .slice slice1 }],
        #[{ fift := "B1", lean := .builder builder1 }],
        #[{ fift := "T1", lean := .tuple tuple1 }],
        mkIntStackAsc 4,
        mkIntStackDesc 4,
        mkStackMixed 4,
        mkIntStackAsc 8,
        mkStackMixed 8
      ]
    let progChoices : Array InitArg := #[progRet, progPush7Ret]

    -- Deterministic expansion.
    for st in stackSeeds do
      if cases.size >= casesWanted then
        break
      for p in progChoices do
        if cases.size >= casesWanted then
          break
        let init0 := mkInitSimple st p
        if !caseExists 0 init0 then
          cases := cases.push (0, code0, init0)
        match code1? with
        | some code1 =>
            let init1 := mkInitSimple st p
            if !caseExists 1 init1 then
              cases := cases.push (1, code1, init1)
        | none => pure ()
        match code511? with
        | some code511 =>
            let rvs : Array Nat := #[0, 1, 2, st.size, st.size + 1]
            for rv in rvs do
              if cases.size >= casesWanted then
                break
              let init511 := mkInitMode511 st p rv
              if !caseExists 511 init511 then
                cases := cases.push (511, code511, init511)
        | none => pure ()

    -- Seeded random expansion to keep RUNVM coverage high when `--cases` is large.
    if cases.size < casesWanted then
      let mut modePool : Array Nat := #[]
      for (m, _c) in codePairs do
        if m < 512 && !(modePool.contains m) then
          modePool := modePool.push m
      if modePool.isEmpty then
        modePool := #[0]
      let mut rng : Rng64 := { state := mixSeed rowSeed "runvm-cases" }
      let mut bump : Nat := 0
      let budget : Nat := casesWanted * 48 + 256
      while cases.size < casesWanted && bump < budget do
        let (mi, rng1) := rng.nextNat modePool.size
        let mode := modePool[mi]!
        let (pi, rng2) := rng1.nextNat progChoices.size
        let prog := progChoices[pi]!
        let (stRand, rng3) := randStack rng2 0 8
        let code? : Option Cell := findCode? mode
        match code? with
        | none =>
            rng := rng3
        | some code =>
            if mode == 511 then
              let (rv, rng4) := rng3.nextNat (stRand.size + 4)
              let init511 := mkInitMode511 stRand prog rv
              if !caseExists 511 init511 then
                cases := cases.push (511, code, init511)
              rng := rng4
            else if mode == 510 then
              let (pick, rng4) := rng3.nextNat 4
              let init510 : Array InitArg :=
                match pick with
                | 0 => #[]
                | 1 => #[mkIntArg (Int.ofNat stRand.size), prog]
                | 2 => stRand ++ #[mkIntArg (Int.ofNat stRand.size), prog]
                | _ =>
                    stRand ++ #[mkIntArg (Int.ofNat stRand.size), prog, mkIntArg 0, { fift := "C1", lean := .cell cell1 }]
                  if !caseExists 510 init510 then
                    cases := cases.push (510, code, init510)
                  rng := rng4
                else
                  let (rv, rng4) := rng3.nextNat (stRand.size + 4)
                  let initN := mkInitForMode stRand prog mode rv
                  if !caseExists mode initN then
                    cases := cases.push (mode, code, initN)
                  rng := rng4
        bump := bump + 1

    cases := cases.take casesWanted
    if cases.size < minCasesPerInstr then
      die s!"RUNVM: generated only {cases.size} cases (< min {minCasesPerInstr}); increase --cases/--variants/--code-variants"

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
      let (c4Out, c5Out) := leanOutCells stF
      let c4HashLean : String := hashHex (Cell.hashBytes c4Out)
      let c5HashLean : String := hashHex (Cell.hashBytes c5Out)
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
          let leanDump := String.intercalate " | " stackLeanTop.toList
          let oracleDump := String.intercalate " | " oracle.stackTop.toList
          die s!"RUNVM (case {cidx+1}, mode={mode}): STACK mismatch at idx={i} lean='{a}' oracle='{b}'\nlean_stack_top={leanDump}\noracle_stack_top={oracleDump}"
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
          mkStackMixed needMax,
          mkIntStackAsc (needMax + 1),
          mkIntStackDesc (needMax + 1),
          mkStackMixed (needMax + 1)
        ]
      if needMax > 0 then
        stacks := stacks.push (mkIntStackAsc (needMax - 1))
        stacks := stacks.push (mkIntStackDesc (needMax - 1))
        stacks := stacks.push (mkStackMixed (needMax - 1))
      stacks := stacks ++
        #[
          mkIntStackAsc (needMax + 2),
          mkIntStackDesc (needMax + 2),
          mkStackMixed (needMax + 2),
          mkIntStackAsc (needMax + 8),
          mkIntStackDesc (needMax + 8),
          mkStackMixed (needMax + 8),
          mkIntStackAsc (needMax + 24),
          mkIntStackDesc (needMax + 24),
          mkStackMixed (needMax + 24),
          #[{ fift := "C1", lean := .cell cell1 }],
          #[{ fift := "S1", lean := .slice slice1 }],
          #[{ fift := "B1", lean := .builder builder1 }],
          #[{ fift := "T1", lean := .tuple tuple1 }],
          #[{ fift := "K1", lean := .cont (.quit 1) }],
          #[]
        ]
      let randNoSigBudget : Nat := Nat.min randomCasesPerInstr (want * 32 + 1024)
      let randNoSig : Array (Array InitArg) :=
        Id.run do
          let mut rng : Rng64 := { state := mixSeed rowSeed "no-sig" }
          let mut out : Array (Array InitArg) := #[]
          for _ in [0:randNoSigBudget] do
            let (pick, rng1) := rng.nextNat 14
            if pick < 8 then
              let (st, rng2) := randStack rng1 needMax (needMax + 24)
              out := out.push st
              rng := rng2
            else if pick < 10 then
              let (st, rng2) := randStack rng1 0 (needMax + 4)
              out := out.push st
              rng := rng2
            else if pick < 12 then
              let maxUf := if needMax == 0 then 1 else needMax
              let (k, rng2) := rng1.nextNat maxUf
              out := out.push (mkIntStackDesc k)
              rng := rng2
            else
              let maxUf := if needMax == 0 then 1 else needMax
              let (k, rng2) := rng1.nextNat maxUf
              let st :=
                if pick % 2 == 0 then
                  mkIntStackAsc k
                else
                  mkStackMixed k
              out := out.push st
              rng := rng2
          out
      stacks := (stackDedup (interleaveArrays stacks randNoSig)).take want
      pure (keptFinal, stacks)
    else
      let inputs := sigInputs row.signature
      let vars ← buildVariants row.name inputs (Nat.max 1 maxStackVariantsPerInstr) randomCasesPerInstr rowSeed
      pure (codePairs, vars)

  let variantsAll := stackDedup (manualVariantsForRow row.name ++ variantsAll)
  let stackVariants := variantsAll.take (Nat.max 1 maxStackVariantsPerInstr)
  let defaultCases : Nat :=
    Nat.max 1 (1 + (stackVariants.size - 1) + (codePairs.size - 1))
  let casesPerInstr : Nat := (casesPerInstr?.getD defaultCases) |> Nat.max 1

  let pushCaseIfFresh (cases : Array (Nat × Nat)) (j i : Nat) : Array (Nat × Nat) :=
    if j < codePairs.size && i < stackVariants.size &&
        !(cases.any (fun (p : Nat × Nat) => p.fst == j && p.snd == i)) then
      cases.push (j, i)
    else
      cases

  let seedNatA : Nat := rowSeed.toNat
  let seedNatB : Nat := (mixSeed rowSeed "case-pairs-diag").toNat

  let mut cases : Array (Nat × Nat) := #[]
  cases := pushCaseIfFresh cases 0 0

  -- Phase A: cover every non-base stack with a non-base code variant when possible.
  if stackVariants.size > 1 then
    for i in [1:stackVariants.size] do
      if cases.size >= casesPerInstr then
        break
      let j : Nat :=
        if codePairs.size <= 1 then
          0
        else
          let span := codePairs.size - 1
          1 + ((i + seedNatA) % span)
      cases := pushCaseIfFresh cases j i

  -- Phase B: still cover each non-base code on the canonical base stack.
  if codePairs.size > 1 then
    for j in [1:codePairs.size] do
      if cases.size >= casesPerInstr then
        break
      cases := pushCaseIfFresh cases j 0

  -- Phase C: deterministic diagonal cross-product sweep to increase mixed coverage.
  if cases.size < casesPerInstr && codePairs.size > 1 && stackVariants.size > 1 then
    let mut t : Nat := 0
    let budget : Nat := casesPerInstr * 8 + 64
    while cases.size < casesPerInstr && t < budget do
      let j : Nat := 1 + (((t * 131) + seedNatA) % (codePairs.size - 1))
      let i : Nat := 1 + (((t * 197) + seedNatB) % (stackVariants.size - 1))
      cases := pushCaseIfFresh cases j i
      t := t + 1

  -- Phase D: exhaustive fallback over the full matrix if still short.
  if cases.size < casesPerInstr then
    for i in [0:stackVariants.size] do
      for j in [0:codePairs.size] do
        if cases.size >= casesPerInstr then
          break
        cases := pushCaseIfFresh cases j i
      if cases.size >= casesPerInstr then
        break

  if cases.size < casesPerInstr && codePairs.size > 0 && stackVariants.size > 0 then
    let mut rng : Rng64 := { state := mixSeed rowSeed ("case-pairs:" ++ row.name) }
    let mut spins : Nat := 0
    let budget : Nat := casesPerInstr * 64 + 256
    while cases.size < casesPerInstr && spins < budget do
      let (j, rng1) := rng.nextNat codePairs.size
      let (i, rng2) := rng1.nextNat stackVariants.size
      cases := pushCaseIfFresh cases j i
      rng := rng2
      spins := spins + 1

  if cases.size < minCasesPerInstr then
    die s!"{row.name}: generated only {cases.size} cases (< min {minCasesPerInstr}); increase --cases/--variants/--code-variants"

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
    let (c4Out, c5Out) := leanOutCells stF
    let c4HashLean : String := hashHex (Cell.hashBytes c4Out)
    let c5HashLean : String := hashHex (Cell.hashBytes c5Out)
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
        let leanDump := String.intercalate " | " stackLeanTop.toList
        let oracleDump := String.intercalate " | " oracle.stackTop.toList
        die s!"{row.name} (case {cidx+1}): STACK mismatch at idx={i} lean='{a}' oracle='{b}'\nlean_stack_top={leanDump}\noracle_stack_top={oracleDump}"

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
  let minCasesPerInstr : Nat :=
    match args.dropWhile (· != "--min-cases") with
    | _ :: n :: _ => n.toNat?.getD 10
    | _ => 10
  let randomCasesPerInstr : Nat :=
    match args.dropWhile (· != "--random-cases") with
    | _ :: n :: _ => n.toNat?.getD 0
    | _ => 0
  let seed : UInt64 :=
    match args.dropWhile (· != "--seed") with
    | _ :: n :: _ => UInt64.ofNat (n.toNat?.getD 1)
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
    validateRow r variantsPerInstr codeVariantsPerInstr casesPerInstr? verbose maxNoSigDepth minCasesPerInstr
      randomCasesPerInstr seed

  IO.println "ok"
  return 0

end TvmLeanOracleValidate
