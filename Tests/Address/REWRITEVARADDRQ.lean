-- Auto-generated stub for TVM instruction REWRITEVARADDRQ (category: address).
import Tests.Registry

open TvmLean Tests

def mkAnycastNothingBits_rewriteVarAddrQ : BitString := #[false]

def mkAnycastJustBits_rewriteVarAddrQ (depth : Nat) (pfx : BitString) : BitString :=
  #[true] ++ natToBits depth (natLenBits 30) ++ pfx

def mkMsgAddrStd_rewriteVarAddrQ (anycast : BitString) (workchain : Int) (addr256 : BitString) : Cell :=
  let wcBits :=
    match intToBitsTwos workchain 8 with
    | .ok bs => bs
    | .error _ => #[]
  Cell.mkOrdinary (natToBits 2 2 ++ anycast ++ wcBits ++ addr256) #[]

def mkMsgAddrVar_rewriteVarAddrQ (anycast : BitString) (workchain : Int) (addr : BitString) : Cell :=
  let wcBits :=
    match intToBitsTwos workchain 32 with
    | .ok bs => bs
    | .error _ => #[]
  Cell.mkOrdinary (natToBits 3 2 ++ anycast ++ natToBits addr.size 9 ++ wcBits ++ addr) #[]

def runRewriteVarAddrQ (s : Slice) (fuel : Nat := 50) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [.tonEnvOp (.rewriteVarAddr true)] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := #[.slice s] }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError "rewritevaraddrq: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def testRewriteVarAddrQ : IO Unit := do
  -- Success: pushes workchain, rewritten slice, -1.
  let pfx : BitString := #[true, false, true, false, true] -- depth=5
  let anycast := mkAnycastJustBits_rewriteVarAddrQ 5 pfx
  let addrBytes : Array UInt8 := Array.replicate 32 0x00
  let addrBits : BitString := (cellOfBytes addrBytes).bits
  let std : Cell := mkMsgAddrStd_rewriteVarAddrQ anycast 0 addrBits
  let expectedBits : BitString := pfx ++ addrBits.drop pfx.size
  let expectedSlice : Slice := Slice.ofCell (Cell.mkOrdinary expectedBits #[])

  let (code0, st0) ← runRewriteVarAddrQ (Slice.ofCell std)
  assert (code0 == -1) s!"rewritevaraddrq(ok): unexpected exitCode={code0}"
  assert (st0.stack.size == 3) s!"rewritevaraddrq(ok): unexpected stack size={st0.stack.size}"
  match st0.stack[0]!, st0.stack[1]!, st0.stack[2]! with
  | .int (.num wc), .slice s', .int (.num status) =>
      assert (wc == 0) s!"rewritevaraddrq(ok): expected wc=0, got {wc}"
      assert (s' == expectedSlice) s!"rewritevaraddrq(ok): unexpected slice (bits={s'.bitsRemaining})"
      assert (status == -1) s!"rewritevaraddrq(ok): expected status=-1, got {status}"
  | a, b, c =>
      throw (IO.userError s!"rewritevaraddrq(ok): unexpected stack values {a.pretty}, {b.pretty}, {c.pretty}")

  -- Failure: prefix longer than address -> pushes 0.
  let pfx6 : BitString := #[true, true, true, true, true, true]
  let anycast6 := mkAnycastJustBits_rewriteVarAddrQ 6 pfx6
  let shortAddr : BitString := #[true, false, true, false, true] -- 5 bits
  let shortVar : Cell := mkMsgAddrVar_rewriteVarAddrQ anycast6 0 shortAddr
  let (code1, st1) ← runRewriteVarAddrQ (Slice.ofCell shortVar)
  assert (code1 == -1) s!"rewritevaraddrq(fail): unexpected exitCode={code1}"
  assert (st1.stack.size == 1) s!"rewritevaraddrq(fail): unexpected stack size={st1.stack.size}"
  assert (st1.stack[0]! == .int (.num 0)) s!"rewritevaraddrq(fail): expected 0, got {st1.stack[0]!.pretty}"

initialize
  Tests.registerTest "address/rewritevaraddrq" testRewriteVarAddrQ
  Tests.registerRoundtrip (.tonEnvOp (.rewriteVarAddr true))
