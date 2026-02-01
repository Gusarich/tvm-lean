-- Auto-generated stub for TVM instruction CHKSIGNU (category: crypto).
import Tests.Registry

open TvmLean Tests

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

initialize
  Tests.registerTest "crypto/chksignu" testChkSignU
  Tests.registerRoundtrip (.chkSignU)
