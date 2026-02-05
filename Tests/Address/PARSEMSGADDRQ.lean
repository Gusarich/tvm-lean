-- Auto-generated stub for TVM instruction PARSEMSGADDRQ (category: address).
import Tests.Registry

open TvmLean Tests

def mkAnycastNothingBits_parseMsgAddrQ : BitString := #[false]

def mkAnycastJustBits_parseMsgAddrQ (depth : Nat) (pfx : BitString) : BitString :=
  #[true] ++ natToBits depth (natLenBits 30) ++ pfx

def mkMsgAddrStd_parseMsgAddrQ (anycast : BitString) (workchain : Int) (addr256 : BitString) : Cell :=
  let wcBits :=
    match intToBitsTwos workchain 8 with
    | .ok bs => bs
    | .error _ => #[]
  Cell.mkOrdinary (natToBits 2 2 ++ anycast ++ wcBits ++ addr256) #[]

def runParseMsgAddrQ (s : Slice) (fuel : Nat := 50) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [.tonEnvOp (.parseMsgAddr true)] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := #[.slice s] }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError "parsemsgaddrq: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def testParseMsgAddrQ : IO Unit := do
  -- Success: pushes tuple and -1.
  let addrBytes : Array UInt8 := Array.replicate 32 0x11
  let addrBits : BitString := (cellOfBytes addrBytes).bits
  let std : Cell := mkMsgAddrStd_parseMsgAddrQ mkAnycastNothingBits_parseMsgAddrQ 0 addrBits
  let (code0, st0) ← runParseMsgAddrQ (Slice.ofCell std)
  assert (code0 == -1) s!"parsemsgaddrq(ok): unexpected exitCode={code0}"
  assert (st0.stack.size == 2) s!"parsemsgaddrq(ok): unexpected stack size={st0.stack.size}"
  match st0.stack[0]!, st0.stack[1]! with
  | .tuple t, .int (.num status) =>
      assert (status == -1) s!"parsemsgaddrq(ok): expected status=-1, got {status}"
      let expectedT : Array Value :=
        #[.int (.num 2), .null, .int (.num 0), .slice (Slice.ofCell (cellOfBytes addrBytes))]
      assert (t == expectedT) s!"parsemsgaddrq(ok): unexpected tuple {st0.stack[0]!.pretty}"
  | a, b => throw (IO.userError s!"parsemsgaddrq(ok): unexpected stack values {a.pretty}, {b.pretty}")

  -- Failure: trailing bits -> pushes 0 instead of throwing.
  let badCell : Cell := Cell.mkOrdinary (std.bits ++ #[true]) #[]
  let (code1, st1) ← runParseMsgAddrQ (Slice.ofCell badCell)
  assert (code1 == -1) s!"parsemsgaddrq(trailing): unexpected exitCode={code1}"
  assert (st1.stack.size == 1) s!"parsemsgaddrq(trailing): unexpected stack size={st1.stack.size}"
  assert (st1.stack[0]! == .int (.num 0)) s!"parsemsgaddrq(trailing): expected 0, got {st1.stack[0]!.pretty}"

  -- Failure: anycast with depth=0 is invalid -> pushes 0.
  let badAnycast : BitString := mkAnycastJustBits_parseMsgAddrQ 0 #[]
  let badStd : Cell := mkMsgAddrStd_parseMsgAddrQ badAnycast 0 addrBits
  let (code2, st2) ← runParseMsgAddrQ (Slice.ofCell badStd)
  assert (code2 == -1) s!"parsemsgaddrq(anycast-depth0): unexpected exitCode={code2}"
  assert (st2.stack.size == 1) s!"parsemsgaddrq(anycast-depth0): unexpected stack size={st2.stack.size}"
  assert (st2.stack[0]! == .int (.num 0)) s!"parsemsgaddrq(anycast-depth0): expected 0, got {st2.stack[0]!.pretty}"

initialize
  Tests.registerTest "address/parsemsgaddrq" testParseMsgAddrQ
  Tests.registerRoundtrip (.tonEnvOp (.parseMsgAddr true))
