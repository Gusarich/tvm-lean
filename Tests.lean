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
  let cell : Cell := Cell.mkOrdinary bs #[]
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
  let base := VmState.initial codeCell
  let st0 : VmState := { base with regs := { base.regs with c4 := initC4 } }
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
  let base := VmState.initial codeCell
  let st0 : VmState := { base with regs := { base.regs with c4 := initC4 } }
  match VmState.run 200 st0 with
  | .continue _ =>
      throw (IO.userError "boc counter: did not halt (fuel exhausted?)")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"boc counter: unexpected exitCode={exitCode}"
      assert (bitsToNat st.regs.c4.bits == 42) s!"boc counter: unexpected c4={bitsToNat st.regs.c4.bits}"

def testBocArithSample : IO Unit := do
  let bytes ← readHexFile "fixtures/inv_opcode.boc.hex"
  let codeCell ←
    match stdBocDeserialize bytes with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"boc arith_sample: failed to parse: {e}")
  let st0 : VmState := VmState.initial codeCell
  match VmState.run 50 st0 with
  | .continue _ =>
      throw (IO.userError "boc arith_sample: did not halt (fuel exhausted?)")
  | .halt exitCode st => do
      assert (exitCode == -1) s!"boc arith_sample: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"boc arith_sample: expected stack size=1, got {st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 11) s!"boc arith_sample: expected 11, got {n}"
      | v => throw (IO.userError s!"boc arith_sample: unexpected stack value {v.pretty}")

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

def testBocParseSamples : IO Unit := do
  let samples : List String :=
    [ "B5EE9C7201010101000800000C7A801401A5A1"
    , "B5EE9C724101010100060000087A801401C8DE68DB"
    ]
  for hex in samples do
    match byteArrayOfHex? hex with
    | .error e => throw (IO.userError s!"boc sample hex parse failed: {e}")
    | .ok bytes =>
        match stdBocDeserialize bytes with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"boc sample failed to parse: {e}")
def testBocSerializeMatchesCanonical : IO Unit := do
  let samples : List (String × Option System.FilePath) :=
    [ ("fixtures/counter.boc.hex", some "fixtures/counter.boc.hex")
    , ("fixtures/inv_opcode.boc.hex", some "fixtures/inv_opcode.boc.hex")
    , ("fixtures/crc32c_ok.boc.hex", some "fixtures/crc32c_ok.boc.hex")
    , ("B5EE9C7201010101000800000C7A801401A5A1", none)
    , ("B5EE9C724101010100060000087A801401C8DE68DB", none)
    ]

  for (label, file?) in samples do
    let hexRaw ←
      match file? with
      | some p => IO.FS.readFile p
      | none => pure label
    let hex := hexRaw.trim

    let bytes ←
      match byteArrayOfHex? hex with
      | .ok b => pure b
      | .error e => throw (IO.userError s!"boc({label}): bad hex: {e}")

    let hdr ←
      match parseBocHeader bytes with
      | .ok h => pure h
      | .error e => throw (IO.userError s!"boc({label}): header parse failed: {e}")
    let opts := BocSerializeOpts.ofHeader hdr

    let root ←
      match stdBocDeserialize bytes with
      | .ok c => pure c
      | .error e => throw (IO.userError s!"boc({label}): stdBocDeserialize failed: {e}")

    let ours ←
      match stdBocSerialize root opts with
      | .ok b => pure b
      | .error e => throw (IO.userError s!"boc({label}): stdBocSerialize failed: {e}")

    assert (ours == bytes) s!"boc({label}): stdBocSerialize differs from canonical input"

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

def testShifts : IO Unit := do
  let progL : List Instr := [ .pushInt (.num 1), .pushInt (.num 5), .lshift ]
  match (← runProg progL) with
  | .continue _ => throw (IO.userError "lshift: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"lshift: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"lshift: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 32) s!"lshift: expected 32, got {n}"
      | v => throw (IO.userError s!"lshift: unexpected stack value {v.pretty}")

  let progR : List Instr := [ .pushInt (.num 32), .pushInt (.num 5), .rshift ]
  match (← runProg progR) with
  | .continue _ => throw (IO.userError "rshift: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"rshift: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"rshift: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1) s!"rshift: expected 1, got {n}"
      | v => throw (IO.userError s!"rshift: unexpected stack value {v.pretty}")

def testDec : IO Unit := do
  let progPos : List Instr := [ .pushInt (.num 10), .dec ]
  match (← runProg progPos) with
  | .continue _ => throw (IO.userError "dec(pos): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"dec(pos): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"dec(pos): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 9) s!"dec(pos): expected 9, got {n}"
      | v => throw (IO.userError s!"dec(pos): unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-1)), .dec ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "dec(neg): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"dec(neg): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"dec(neg): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -2) s!"dec(neg): expected -2, got {n}"
      | v => throw (IO.userError s!"dec(neg): unexpected stack value {v.pretty}")

def testAdd : IO Unit := do
  let progPos : List Instr := [ .pushInt (.num 7), .pushInt (.num 5), .add ]
  match (← runProg progPos) with
  | .continue _ => throw (IO.userError "add(pos): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"add(pos): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"add(pos): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 12) s!"add(pos): expected 12, got {n}"
      | v => throw (IO.userError s!"add(pos): unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-3)), .pushInt (.num 10), .add ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "add(neg): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"add(neg): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"add(neg): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 7) s!"add(neg): expected 7, got {n}"
      | v => throw (IO.userError s!"add(neg): unexpected stack value {v.pretty}")

def testSub : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 10), .pushInt (.num 4), .sub ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "sub: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"sub: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"sub: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 6) s!"sub: expected 6, got {n}"
      | v => throw (IO.userError s!"sub: unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-3)), .pushInt (.num 5), .sub ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "sub(neg): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"sub(neg): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"sub(neg): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -8) s!"sub(neg): expected -8, got {n}"
      | v => throw (IO.userError s!"sub(neg): unexpected stack value {v.pretty}")

def testTuplePush : IO Unit := do
  let prog : List Instr :=
    [ .pushInt (.num 1)
    , .pushInt (.num 2)
    , .tupleOp (.mktuple 2)
    , .pushInt (.num 3)
    , .tupleOp .tpush
    ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "tpush: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"tpush: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"tpush: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .tuple items =>
          assert (items.size == 3) s!"tpush: expected tuple size=3, got {items.size}"
          match items[0]!, items[1]!, items[2]! with
          | .int (.num a), .int (.num b), .int (.num c) =>
              assert (a == 1 ∧ b == 2 ∧ c == 3) s!"tpush: expected [1,2,3], got {items.map (·.pretty)}"
          | _, _, _ =>
              throw (IO.userError s!"tpush: unexpected tuple contents {items.map (·.pretty)}")
      | v =>
          throw (IO.userError s!"tpush: unexpected stack value {v.pretty}")

def testBuilderBits : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 1), .newc, .stu 1, .bbits ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "bbits: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"bbits: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"bbits: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1) s!"bbits: expected 1, got {n}"
      | v => throw (IO.userError s!"bbits: unexpected stack value {v.pretty}")

def testInc : IO Unit := do
  let progPos : List Instr := [ .pushInt (.num 41), .inc ]
  match (← runProg progPos) with
  | .continue _ => throw (IO.userError "inc(pos): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"inc(pos): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"inc(pos): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 42) s!"inc(pos): expected 42, got {n}"
      | v => throw (IO.userError s!"inc(pos): unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-2)), .inc ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "inc(neg): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"inc(neg): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"inc(neg): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -1) s!"inc(neg): expected -1, got {n}"
      | v => throw (IO.userError s!"inc(neg): unexpected stack value {v.pretty}")

def cellOfBytes (bs : Array UInt8) : Cell :=
  Id.run do
    let mut bits : BitString := #[]
    for b in bs do
      bits := bits ++ natToBits b.toNat 8
    Cell.mkOrdinary bits #[]

def testXctosIsSpecial : IO Unit := do
  let codeCell ←
    match assembleCp0 [ .xctos ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let base := VmState.initial codeCell

  -- Ordinary cell → is_special=false (0)
  let ordinary : Cell := cellOfBytes #[0xaa]
  let st0Ord : VmState := { base with stack := #[.cell ordinary] }
  match VmState.run 20 st0Ord with
  | .continue _ => throw (IO.userError "xctos(ordinary): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"xctos(ordinary): unexpected exitCode={exitCode}"
      assert (st.stack.size == 2) s!"xctos(ordinary): expected stack size=2, got {st.stack.size}"
      match st.stack[0]!, st.stack[1]! with
      | .slice _, .int (.num n) => assert (n == 0) s!"xctos(ordinary): expected 0, got {n}"
      | a, b => throw (IO.userError s!"xctos(ordinary): unexpected stack [{a.pretty}, {b.pretty}]")

  -- Library exotic cell → is_special=true (-1)
  let hashBytes : Array UInt8 := Array.replicate 32 0
  let libOrd : Cell := cellOfBytes (#[UInt8.ofNat 2] ++ hashBytes)
  let lib : Cell := { libOrd with special := true, levelMask := 0 }
  let st0Lib : VmState := { base with stack := #[.cell lib] }
  match VmState.run 20 st0Lib with
  | .continue _ => throw (IO.userError "xctos(library): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"xctos(library): unexpected exitCode={exitCode}"
      assert (st.stack.size == 2) s!"xctos(library): expected stack size=2, got {st.stack.size}"
      match st.stack[0]!, st.stack[1]! with
      | .slice _, .int (.num n) => assert (n == -1) s!"xctos(library): expected -1, got {n}"
      | a, b => throw (IO.userError s!"xctos(library): unexpected stack [{a.pretty}, {b.pretty}]")

def testChkSignU : IO Unit := do
  -- Fixed Ed25519 test vector: seed=0..31, msg=32 bytes, signature over msg.
  let pkHex := "03a107bff3ce10be1d70dd18e74bc09967e4d6309ba50d5f1ddc8664125531b8"
  let msgHex := "54564d4c45414e5f454432353531395f544553545f564543544f525f5f000000"
  let sigHex := "7eba76991a02f84a84f0918da018fe28a26db22adcffcd9ac6b88c035de6bdf51abf731ca7bcffbcd204d89f780df78ea088862af234719c525ad2b2b1985b03"

  let pkBa ←
    match byteArrayOfHex? pkHex with
    | .ok ba => pure ba
    | .error e => throw (IO.userError s!"chksignu: bad pk hex: {e}")
  let msgBa ←
    match byteArrayOfHex? msgHex with
    | .ok ba => pure ba
    | .error e => throw (IO.userError s!"chksignu: bad msg hex: {e}")
  let sigBa ←
    match byteArrayOfHex? sigHex with
    | .ok ba => pure ba
    | .error e => throw (IO.userError s!"chksignu: bad sig hex: {e}")

  let keyNat := bytesToNatBE pkBa.data
  let hashNat := bytesToNatBE msgBa.data
  let sigSlice : Slice := Slice.ofCell (cellOfBytes sigBa.data)

  let codeCell ←
    match assembleCp0 [ .chkSignU ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let base := VmState.initial codeCell
  let st0 : VmState :=
    { base with stack := #[.int (.num (Int.ofNat hashNat)), .slice sigSlice, .int (.num (Int.ofNat keyNat))] }

  match VmState.run 20 st0 with
  | .continue _ => throw (IO.userError "chksignu: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"chksignu: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"chksignu: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -1) s!"chksignu: expected -1, got {n}"
      | v => throw (IO.userError s!"chksignu: unexpected stack value {v.pretty}")

  -- Corrupt signature → false.
  let b0 := sigBa.data[0]!
  let sigBad := sigBa.data.set! 0 (UInt8.ofNat ((b0.toNat + 1) % 256))
  let sigBadSlice : Slice := Slice.ofCell (cellOfBytes sigBad)
  let stBad : VmState :=
    { base with stack := #[.int (.num (Int.ofNat hashNat)), .slice sigBadSlice, .int (.num (Int.ofNat keyNat))] }
  match VmState.run 20 stBad with
  | .continue _ => throw (IO.userError "chksignu(bad): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"chksignu(bad): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"chksignu(bad): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 0) s!"chksignu(bad): expected 0, got {n}"
      | v => throw (IO.userError s!"chksignu(bad): unexpected stack value {v.pretty}")

def msgForwardPricesCell (firstFrac : Nat) : Cell :=
  -- msg_forward_prices#ea lump_price:uint64 bit_price:uint64 cell_price:uint64 ihr_price_factor:uint32
  --                  first_frac:uint16 next_frac:uint16 = MsgForwardPrices;
  let bits :=
    natToBits 0xea 8 ++
    natToBits 0 64 ++
    natToBits 0 64 ++
    natToBits 0 64 ++
    natToBits 0 32 ++
    natToBits firstFrac 16 ++
    natToBits 0 16
  Cell.mkOrdinary bits #[]

def testGetOriginalFwdFee : IO Unit := do
  let prog : List Instr := [ .getOriginalFwdFee ]
  let codeCell ←
    match assembleCp0 prog with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")

  let mcPrices := msgForwardPricesCell 1000
  let basePrices := msgForwardPricesCell 2000
  let unpackedCfg : Array Value :=
    (Array.replicate 7 Value.null)
      |>.set! 4 (.slice (Slice.ofCell mcPrices))
      |>.set! 5 (.slice (Slice.ofCell basePrices))
  let params : Array Value :=
    (Array.replicate 15 Value.null)
      |>.set! 14 (.tuple unpackedCfg)
  let c7 : Array Value := #[.tuple params]

  let base := VmState.initial codeCell

  -- is_masterchain = true
  let stMc : VmState := { base with stack := #[.int (.num 1000), .int (.num (-1))], regs := { base.regs with c7 := c7 } }
  match VmState.run 20 stMc with
  | .continue _ => throw (IO.userError "getoriginalfwdfee(mc): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"getoriginalfwdfee(mc): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"getoriginalfwdfee(mc): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1015) s!"getoriginalfwdfee(mc): expected 1015, got {n}"
      | v => throw (IO.userError s!"getoriginalfwdfee(mc): unexpected stack value {v.pretty}")

  -- is_masterchain = false
  let stBase : VmState := { base with stack := #[.int (.num 1000), .int (.num 0)], regs := { base.regs with c7 := c7 } }
  match VmState.run 20 stBase with
  | .continue _ => throw (IO.userError "getoriginalfwdfee(base): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"getoriginalfwdfee(base): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"getoriginalfwdfee(base): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1031) s!"getoriginalfwdfee(base): expected 1031, got {n}"
      | v => throw (IO.userError s!"getoriginalfwdfee(base): unexpected stack value {v.pretty}")

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
  roundtrip (.lshift)
  roundtrip (.rshift)
  roundtrip (.add)
  roundtrip (.tupleOp .tpush)
  roundtrip (.boolAnd)
  roundtrip (.boolOr)
  roundtrip (.composBoth)
  roundtrip (.bbits)
  roundtrip (.dec)
  roundtrip (.try_)
  roundtrip (.sub)
  roundtrip (.chkSignU)
  roundtrip (.chkSignS)
  roundtrip (.getOriginalFwdFee)
  testCounter
  testBocCounter
  testBocArithSample
  testBocCrc32cOk
  testBocParseSamples
  testBocSerializeMatchesCanonical
  testEqual
  testIfNotRet
  testSetCp
  testShifts
  testDec
  testAdd
  testSub
  testTuplePush
  testBuilderBits
  testInc
  testXctosIsSpecial
  testChkSignU
  testGetOriginalFwdFee
  IO.println "ok"
