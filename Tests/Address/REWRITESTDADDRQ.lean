-- Auto-generated stub for TVM instruction REWRITESTDADDRQ (category: address).
import Tests.Registry

open TvmLean Tests

def mkAnycastNothingBits_rewriteStdAddrQ : BitString := #[false]

def mkMsgAddrStd_rewriteStdAddrQ (anycast : BitString) (workchain : Int) (addr256 : BitString) : Cell :=
  let wcBits :=
    match intToBitsTwos workchain 8 with
    | .ok bs => bs
    | .error _ => #[]
  Cell.mkOrdinary (natToBits 2 2 ++ anycast ++ wcBits ++ addr256) #[]

def mkMsgAddrVar_rewriteStdAddrQ (anycast : BitString) (workchain : Int) (addr : BitString) : Cell :=
  let wcBits :=
    match intToBitsTwos workchain 32 with
    | .ok bs => bs
    | .error _ => #[]
  Cell.mkOrdinary (natToBits 3 2 ++ anycast ++ natToBits addr.size 9 ++ wcBits ++ addr) #[]

def runRewriteStdAddrQ (s : Slice) (fuel : Nat := 50) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [.tonEnvOp (.rewriteStdAddr true)] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := #[.slice s] }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError "rewritestdaddrq: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def testRewriteStdAddrQ : IO Unit := do
  -- Success: pushes workchain, hash, -1.
  let addrBytes : Array UInt8 := Array.replicate 32 0x02
  let addrBits : BitString := (cellOfBytes addrBytes).bits
  let std : Cell := mkMsgAddrStd_rewriteStdAddrQ mkAnycastNothingBits_rewriteStdAddrQ 0 addrBits
  let expectedHash : Int := Int.ofNat (bitsToNat addrBits)

  let (code0, st0) ← runRewriteStdAddrQ (Slice.ofCell std)
  assert (code0 == -1) s!"rewritestdaddrq(ok): unexpected exitCode={code0}"
  assert (st0.stack.size == 3) s!"rewritestdaddrq(ok): unexpected stack size={st0.stack.size}"
  match st0.stack[0]!, st0.stack[1]!, st0.stack[2]! with
  | .int (.num wc), .int (.num hash), .int (.num status) =>
      assert (wc == 0) s!"rewritestdaddrq(ok): expected wc=0, got {wc}"
      assert (hash == expectedHash) s!"rewritestdaddrq(ok): expected hash={expectedHash}, got {hash}"
      assert (status == -1) s!"rewritestdaddrq(ok): expected status=-1, got {status}"
  | a, b, c =>
      throw (IO.userError s!"rewritestdaddrq(ok): unexpected stack values {a.pretty}, {b.pretty}, {c.pretty}")

  -- Failure: msg_addr_var with non-256 length -> pushes 0 (no exception).
  let shortVarAddr : BitString := #[true, false, true, false, true, false, true] -- 7 bits
  let varShort : Cell := mkMsgAddrVar_rewriteStdAddrQ mkAnycastNothingBits_rewriteStdAddrQ 0 shortVarAddr
  let (code1, st1) ← runRewriteStdAddrQ (Slice.ofCell varShort)
  assert (code1 == -1) s!"rewritestdaddrq(fail): unexpected exitCode={code1}"
  assert (st1.stack.size == 1) s!"rewritestdaddrq(fail): unexpected stack size={st1.stack.size}"
  assert (st1.stack[0]! == .int (.num 0)) s!"rewritestdaddrq(fail): expected 0, got {st1.stack[0]!.pretty}"

initialize
  Tests.registerTest "address/rewritestdaddrq" testRewriteStdAddrQ
  Tests.registerRoundtrip (.tonEnvOp (.rewriteStdAddr true))
