-- Auto-generated stub for TVM instruction SHA256U (category: crypto).
import Tests.Registry

open TvmLean Tests

def runSha256U (s : Slice) (fuel : Nat := 50) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [.cryptoOp .sha256U] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := #[.slice s] }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError "sha256u: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def testSha256U : IO Unit := do
  -- sha256("abc") = ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
  let msg : Slice := Slice.ofCell (cellOfBytes #[0x61, 0x62, 0x63])
  let expectedBytes : ByteArray ←
    match byteArrayOfHex? "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" with
    | .ok ba => pure ba
    | .error e => throw (IO.userError s!"sha256u: bad expected hex: {e}")
  let expected : Int := Int.ofNat (byteArrayToNatBE expectedBytes)

  let (code0, st0) ← runSha256U msg
  assert (code0 == -1) s!"sha256u: unexpected exitCode={code0}"
  assert (st0.stack.size == 1) s!"sha256u: unexpected stack size={st0.stack.size}"
  match st0.stack[0]! with
  | .int (.num h) => assert (h == expected) s!"sha256u: unexpected hash {h}"
  | v => throw (IO.userError s!"sha256u: unexpected stack value {v.pretty}")

  -- Non-byte-aligned slice: throws cellUnd.
  let oneBit : Cell := Cell.mkOrdinary (natToBits 1 1) #[]
  let (code1, _st1) ← runSha256U (Slice.ofCell oneBit)
  assert (code1 == (~~~ Excno.cellUnd.toInt)) s!"sha256u(unaligned): expected cellUnd, got exitCode={code1}"

initialize
  Tests.registerTest "crypto/sha256u" testSha256U
  Tests.registerRoundtrip (.cryptoOp .sha256U)
