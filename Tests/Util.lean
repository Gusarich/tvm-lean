import TvmLean

open TvmLean

namespace Tests

def assert (b : Bool) (msg : String) : IO Unit := do
  if b then
    pure ()
  else
    throw (IO.userError msg)

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then
    some (10 + (c.toNat - 'a'.toNat))
  else if 'A' ≤ c ∧ c ≤ 'F' then
    some (10 + (c.toNat - 'A'.toNat))
  else
    none

def byteArrayOfHex? (hex : String) : Except String ByteArray := do
  let s := hex.trim
  let chars := s.data.toArray
  if chars.size % 2 ≠ 0 then
    throw s!"hex length must be even, got {chars.size}"
  let mut out : Array UInt8 := #[]
  for i in [0:(chars.size / 2)] do
    let a := chars[2 * i]!
    let b := chars[2 * i + 1]!
    let hi ←
      match hexVal a with
      | some v => pure v
      | none => throw s!"invalid hex digit '{a}'"
    let lo ←
      match hexVal b with
      | some v => pure v
      | none => throw s!"invalid hex digit '{b}'"
    out := out.push (UInt8.ofNat (hi * 16 + lo))
  return ByteArray.mk out

def readHexFile (path : System.FilePath) : IO ByteArray := do
  let s ← IO.FS.readFile path
  match byteArrayOfHex? s with
  | .ok ba => pure ba
  | .error e => throw (IO.userError s!"{path}: {e}")

def roundtrip (i : Instr) : IO Unit := do
  let bs ←
    match encodeCp0 i with
    | .ok bs => pure bs
    | .error e => throw (IO.userError s!"encodeCp0 failed for {reprStr i}: {reprStr e}")
  let cell : Cell := Cell.mkOrdinary bs #[]
  let s := Slice.ofCell cell
  match decodeCp0 s with
  | .error e =>
      throw (IO.userError s!"decodeCp0 failed for {reprStr i}: {reprStr e}")
  | .ok (i', rest) =>
      assert (i' == i) s!"roundtrip mismatch: {reprStr i} ≠ {reprStr i'}"
      assert (rest.bitsRemaining == 0) s!"roundtrip did not consume all bits for {reprStr i}"

def runProg (prog : List Instr) (fuel : Nat := 200) : IO StepResult := do
  let codeCell ←
    match assembleCp0 prog with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 := VmState.initial codeCell
  pure (VmState.run fuel st0)

def cellOfBytes (bs : Array UInt8) : Cell :=
  Id.run do
    let mut bits : BitString := #[]
    for b in bs do
      bits := bits ++ natToBits b.toNat 8
    Cell.mkOrdinary bits #[]

end Tests

