-- Auto-generated stub for TVM instruction REWRITESTDADDR (category: address).
import Tests.Registry

open TvmLean Tests

def mkAnycastNothingBits_rewriteStdAddr : BitString := #[false]

def mkAnycastJustBits_rewriteStdAddr (depth : Nat) (pfx : BitString) : BitString :=
  #[true] ++ natToBits depth (natLenBits 30) ++ pfx

def mkMsgAddrStd_rewriteStdAddr (anycast : BitString) (workchain : Int) (addr256 : BitString) : Cell :=
  let wcBits :=
    match intToBitsTwos workchain 8 with
    | .ok bs => bs
    | .error _ => #[]
  Cell.mkOrdinary (natToBits 2 2 ++ anycast ++ wcBits ++ addr256) #[]

def mkMsgAddrVar_rewriteStdAddr (anycast : BitString) (workchain : Int) (addr : BitString) : Cell :=
  let wcBits :=
    match intToBitsTwos workchain 32 with
    | .ok bs => bs
    | .error _ => #[]
  Cell.mkOrdinary (natToBits 3 2 ++ anycast ++ natToBits addr.size 9 ++ wcBits ++ addr) #[]

def runRewriteStdAddr (s : Slice) (fuel : Nat := 50) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [.tonEnvOp (.rewriteStdAddr false)] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := #[.slice s] }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError "rewritestdaddr: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def testRewriteStdAddr : IO Unit := do
  -- No anycast: returns workchain and 256-bit address as integer.
  let addrBytesA : Array UInt8 := Array.replicate 32 0x01
  let addrBitsA : BitString := (cellOfBytes addrBytesA).bits
  let stdA : Cell := mkMsgAddrStd_rewriteStdAddr mkAnycastNothingBits_rewriteStdAddr 0 addrBitsA
  let expectedHashA : Int := Int.ofNat (bitsToNat addrBitsA)
  let (code0, st0) ← runRewriteStdAddr (Slice.ofCell stdA)
  assert (code0 == -1) s!"rewritestdaddr(no-anycast): unexpected exitCode={code0}"
  assert (st0.stack.size == 2) s!"rewritestdaddr(no-anycast): unexpected stack size={st0.stack.size}"
  match st0.stack[0]!, st0.stack[1]! with
  | .int (.num wc), .int (.num hash) =>
      assert (wc == 0) s!"rewritestdaddr(no-anycast): expected wc=0, got {wc}"
      assert (hash == expectedHashA) s!"rewritestdaddr(no-anycast): expected hash={expectedHashA}, got {hash}"
  | a, b => throw (IO.userError s!"rewritestdaddr(no-anycast): unexpected stack values {a.pretty}, {b.pretty}")

  -- Anycast: replaces first `depth` bits of address with prefix.
  let pfx : BitString := #[true, true, true, true, true] -- depth=5
  let anycast := mkAnycastJustBits_rewriteStdAddr 5 pfx
  let addrBytesB : Array UInt8 := Array.replicate 32 0x00
  let addrBitsB : BitString := (cellOfBytes addrBytesB).bits
  let stdB : Cell := mkMsgAddrStd_rewriteStdAddr anycast (-1) addrBitsB
  let expectedBitsB : BitString := pfx ++ addrBitsB.drop pfx.size
  let expectedHashB : Int := Int.ofNat (bitsToNat expectedBitsB)
  let (code1, st1) ← runRewriteStdAddr (Slice.ofCell stdB)
  assert (code1 == -1) s!"rewritestdaddr(anycast): unexpected exitCode={code1}"
  assert (st1.stack.size == 2) s!"rewritestdaddr(anycast): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num wc), .int (.num hash) =>
      assert (wc == -1) s!"rewritestdaddr(anycast): expected wc=-1, got {wc}"
      assert (hash == expectedHashB) s!"rewritestdaddr(anycast): expected hash={expectedHashB}, got {hash}"
  | a, b => throw (IO.userError s!"rewritestdaddr(anycast): unexpected stack values {a.pretty}, {b.pretty}")

  -- Accepts msg_addr_var only when its length is exactly 256 bits.
  let var256 : Cell := mkMsgAddrVar_rewriteStdAddr mkAnycastNothingBits_rewriteStdAddr (-2) addrBitsA
  let (code2, st2) ← runRewriteStdAddr (Slice.ofCell var256)
  assert (code2 == -1) s!"rewritestdaddr(var256): unexpected exitCode={code2}"
  assert (st2.stack.size == 2) s!"rewritestdaddr(var256): unexpected stack size={st2.stack.size}"
  match st2.stack[0]!, st2.stack[1]! with
  | .int (.num wc), .int (.num hash) =>
      assert (wc == -2) s!"rewritestdaddr(var256): expected wc=-2, got {wc}"
      assert (hash == expectedHashA) s!"rewritestdaddr(var256): expected hash={expectedHashA}, got {hash}"
  | a, b => throw (IO.userError s!"rewritestdaddr(var256): unexpected stack values {a.pretty}, {b.pretty}")

  -- msg_addr_var with non-256 length: throws cellUnd.
  let shortVarAddr : BitString := #[true, false, true, false, true, false, true] -- 7 bits
  let varShort : Cell := mkMsgAddrVar_rewriteStdAddr mkAnycastNothingBits_rewriteStdAddr 0 shortVarAddr
  let (code3, _st3) ← runRewriteStdAddr (Slice.ofCell varShort)
  assert (code3 == (~~~ Excno.cellUnd.toInt)) s!"rewritestdaddr(var-short): expected cellUnd, got exitCode={code3}"

initialize
  Tests.registerTest "address/rewritestdaddr" testRewriteStdAddr
  Tests.registerRoundtrip (.tonEnvOp (.rewriteStdAddr false))
