import TvmLean

open TvmLean

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
  let cell : Cell := { bits := bs, refs := #[] }
  let s := Slice.ofCell cell
  match decodeCp0 s with
  | .error e =>
      throw (IO.userError s!"decodeCp0 failed for {reprStr i}: {reprStr e}")
  | .ok (i', rest) =>
      assert (i' == i) s!"roundtrip mismatch: {reprStr i} ≠ {reprStr i'}"
      assert (rest.bitsRemaining == 0) s!"roundtrip did not consume all bits for {reprStr i}"

def testCounter : IO Unit := do
  let prog : List Instr :=
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
  let codeCell ←
    match assembleCp0 prog with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let initC4 : Cell := Cell.ofUInt 32 41
  let st0 : VmState :=
    { (VmState.initial codeCell) with regs := { (Regs.initial) with c4 := initC4 } }
  match VmState.run 200 st0 with
  | .continue _ =>
      throw (IO.userError "counter: did not halt (fuel exhausted?)")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"counter: unexpected exitCode={exitCode}"
      assert (bitsToNat st.regs.c4.bits == 42) s!"counter: unexpected c4={bitsToNat st.regs.c4.bits}"

def testBocCounter : IO Unit := do
  let bytes ← readHexFile "fixtures/counter.boc.hex"
  let codeCell ←
    match stdBocDeserialize bytes with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"boc counter: failed to parse: {e}")
  let initC4 : Cell := Cell.ofUInt 32 41
  let st0 : VmState :=
    { (VmState.initial codeCell) with regs := { (Regs.initial) with c4 := initC4 } }
  match VmState.run 200 st0 with
  | .continue _ =>
      throw (IO.userError "boc counter: did not halt (fuel exhausted?)")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"boc counter: unexpected exitCode={exitCode}"
      assert (bitsToNat st.regs.c4.bits == 42) s!"boc counter: unexpected c4={bitsToNat st.regs.c4.bits}"

def testBocInvOpcode : IO Unit := do
  let bytes ← readHexFile "fixtures/inv_opcode.boc.hex"
  let codeCell ←
    match stdBocDeserialize bytes with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"boc inv_opcode: failed to parse: {e}")
  let st0 : VmState := VmState.initial codeCell
  match VmState.run 50 st0 with
  | .continue _ =>
      throw (IO.userError "boc inv_opcode: did not halt (fuel exhausted?)")
  | .halt exitCode _ =>
      assert (exitCode == -7) s!"boc inv_opcode: expected exitCode=-7, got {exitCode}"

def testBocCrc32cOk : IO Unit := do
  let bytes ← readHexFile "fixtures/crc32c_ok.boc.hex"
  let codeCell ←
    match stdBocDeserialize bytes with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"boc crc32c_ok: failed to parse: {e}")
  let st0 : VmState := VmState.initial codeCell
  match VmState.run 50 st0 with
  | .continue _ =>
      throw (IO.userError "boc crc32c_ok: did not halt (fuel exhausted?)")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"boc crc32c_ok: unexpected exitCode={exitCode}"
      assert (st.stack.size == 2) s!"boc crc32c_ok: unexpected stack size={st.stack.size}"
      match st.stack[0]!, st.stack[1]! with
      | .int (.num a), .int (.num b) =>
          assert (a == 20 ∧ b == 10) s!"boc crc32c_ok: expected [20,10], got {Stack.pretty st.stack}"
      | _, _ =>
          throw (IO.userError s!"boc crc32c_ok: unexpected stack {Stack.pretty st.stack}")

def runProg (prog : List Instr) (fuel : Nat := 200) : IO StepResult := do
  let codeCell ←
    match assembleCp0 prog with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 := VmState.initial codeCell
  pure (VmState.run fuel st0)

def testEqual : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 10), .pushInt (.num 10), .equal ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "equal: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"equal: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"equal: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -1) s!"equal: expected -1, got {n}"
      | v => throw (IO.userError s!"equal: unexpected stack value {v.pretty}")

def testIfNotRet : IO Unit := do
  -- IFNOTRET returns when flag is false (0); the following PUSHINT must not execute.
  let prog : List Instr := [ .pushInt (.num 0), .ifnotret, .pushInt (.num 99) ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "ifnotret: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"ifnotret: unexpected exitCode={exitCode}"
      assert (st.stack.size == 0) s!"ifnotret: expected empty stack, got {Stack.pretty st.stack}"

def testSetCp : IO Unit := do
  -- SETCP 1 is unsupported in our MVP and must raise inv_opcode (6), i.e. exit ~6 = -7.
  let prog : List Instr := [ .setcp 1 ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "setcp: did not halt")
  | .halt exitCode _ =>
      assert (exitCode == -7) s!"setcp: expected exitCode=-7, got {exitCode}"

def main (_args : List String) : IO Unit := do
  roundtrip (.pushInt (.num 0))
  roundtrip (.pushInt (.num (-5)))
  roundtrip (.pushInt (.num 127))
  roundtrip (.pushInt (.num (-128)))
  roundtrip (.pushInt (.num 20000))
  roundtrip (.pushInt (.num 1000000))
  roundtrip (.push 0)
  roundtrip (.push 7)
  roundtrip (.push 200)
  roundtrip (.pop 0)
  roundtrip (.pop 9)
  roundtrip (.pop 200)
  roundtrip (.xchg0 1)
  roundtrip (.xchg0 15)
  roundtrip (.xchg0 200)
  roundtrip (.ctos)
  roundtrip (.ends)
  roundtrip (.ldu 32)
  roundtrip (.stu 32)
  roundtrip (.newc)
  roundtrip (.endc)
  roundtrip (.inc)
  roundtrip (.equal)
  roundtrip (.throwIfNot 0)
  roundtrip (.throwIfNot 63)
  roundtrip (.throwIfNot 1000)
  roundtrip (.ifret)
  roundtrip (.ifnotret)
  roundtrip (.setcp 0)
  testCounter
  testBocCounter
  testBocInvOpcode
  testBocCrc32cOk
  testEqual
  testIfNotRet
  testSetCp
  IO.println "ok"
