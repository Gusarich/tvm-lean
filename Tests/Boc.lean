import Tests.Registry

open TvmLean Tests

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

initialize
  Tests.registerTest "boc/counter" testBocCounter
  Tests.registerTest "boc/arith_sample" testBocArithSample
  Tests.registerTest "boc/crc32c_ok" testBocCrc32cOk
  Tests.registerTest "boc/parse_samples" testBocParseSamples
  Tests.registerTest "boc/serialize_matches_canonical" testBocSerializeMatchesCanonical
