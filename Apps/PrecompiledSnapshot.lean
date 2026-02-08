import TvmLean.Validation.Diff.Runner

open TvmLean

def hexByte (b : UInt8) : String :=
  let n : Nat := b.toNat
  let hi : Nat := n >>> 4
  let lo : Nat := n &&& 0x0f
  let digit (x : Nat) : Char :=
    if x < 10 then
      Char.ofNat ('0'.toNat + x)
    else
      Char.ofNat ('A'.toNat + (x - 10))
  String.mk [digit hi, digit lo]

def bytesToHex (bs : Array UInt8) : String :=
  String.join (bs.toList.map hexByte)

def mkLibRefCellFromHashBytes (h : Array UInt8) : Cell :=
  Id.run do
    let mut hashBits : BitString := #[]
    for b in h do
      hashBits := hashBits ++ natToBits b.toNat 8
    { bits := natToBits 2 8 ++ hashBits, refs := #[], special := true, levelMask := 0 }

def myCodeCellFromFixtureHeuristic (codeCell : Cell) : Cell :=
  if codeCell.special then
    codeCell
  else if codeCell.bits.size = 80 && codeCell.refs.size = 1 && bitsToNat (codeCell.bits.take 8) = 0xff then
    mkLibRefCellFromHashBytes (Cell.hashBytes codeCell)
  else
    codeCell

def isJsonFile (p : System.FilePath) : Bool :=
  match p.fileName with
  | some name => p.extension == some "json" && !name.startsWith "_"
  | none => false

def main (args : List String) : IO Unit := do
  let dir : System.FilePath :=
    match args with
    | path :: _ => path
    | [] => "diff-test/fixtures-local-2026-01-28-500"

  let files ← dir.walkDir
  let mut total : Nat := 0
  let mut counts : Std.HashMap String Nat := {}
  for f in files do
    if isJsonFile f then
      let tc ← loadTestCase f
      if tc.expected.gas_used == some 1000 then
        match decodeBytes tc.code_boc with
        | .error _ => pure ()
        | .ok codeBytes =>
            match stdBocDeserialize codeBytes with
            | .error _ => pure ()
            | .ok codeCell =>
                total := total + 1
                let myCodeCell := myCodeCellFromFixtureHeuristic codeCell
                let h := bytesToHex (Cell.hashBytes myCodeCell)
                let prev := counts.getD h 0
                counts := counts.insert h (prev + 1)

  let mut entries : Array (String × Nat) := #[]
  for (k, v) in counts.toList do
    entries := entries.push (k, v)
  let entriesSorted := entries.qsort (fun a b => a.2 > b.2)

  IO.println s!"dir={dir} expected_gas_used=1000 cases={total} unique_hashes={entriesSorted.size}"
  for (h, c) in entriesSorted do
    IO.println s!"{c}\t{h}"
