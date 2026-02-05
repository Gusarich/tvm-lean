-- Auto-generated stub for TVM instruction REWRITEVARADDR (category: address).
import Tests.Registry

open TvmLean Tests

def mkAnycastNothingBits_rewriteVarAddr : BitString := #[false]

def mkAnycastJustBits_rewriteVarAddr (depth : Nat) (pfx : BitString) : BitString :=
  #[true] ++ natToBits depth (natLenBits 30) ++ pfx

def mkMsgAddrStd_rewriteVarAddr (anycast : BitString) (workchain : Int) (addr256 : BitString) : Cell :=
  let wcBits :=
    match intToBitsTwos workchain 8 with
    | .ok bs => bs
    | .error _ => #[]
  Cell.mkOrdinary (natToBits 2 2 ++ anycast ++ wcBits ++ addr256) #[]

def mkMsgAddrVar_rewriteVarAddr (anycast : BitString) (workchain : Int) (addr : BitString) : Cell :=
  let wcBits :=
    match intToBitsTwos workchain 32 with
    | .ok bs => bs
    | .error _ => #[]
  Cell.mkOrdinary (natToBits 3 2 ++ anycast ++ natToBits addr.size 9 ++ wcBits ++ addr) #[]

def runRewriteVarAddr (s : Slice) (fuel : Nat := 50) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [.tonEnvOp (.rewriteVarAddr false)] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := #[.slice s] }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError "rewritevaraddr: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def testRewriteVarAddr : IO Unit := do
  -- Std address: returns rewritten slice (still 256 bits).
  let pfx : BitString := #[true, false, true, false, true] -- depth=5
  let anycast := mkAnycastJustBits_rewriteVarAddr 5 pfx
  let addrBytes : Array UInt8 := Array.replicate 32 0x00
  let addrBits : BitString := (cellOfBytes addrBytes).bits
  let std : Cell := mkMsgAddrStd_rewriteVarAddr anycast (-1) addrBits
  let expectedBits : BitString := pfx ++ addrBits.drop pfx.size
  let expectedSlice : Slice := Slice.ofCell (Cell.mkOrdinary expectedBits #[])
  let (code0, st0) ← runRewriteVarAddr (Slice.ofCell std)
  assert (code0 == -1) s!"rewritevaraddr(std): unexpected exitCode={code0}"
  assert (st0.stack.size == 2) s!"rewritevaraddr(std): unexpected stack size={st0.stack.size}"
  match st0.stack[0]!, st0.stack[1]! with
  | .int (.num wc), .slice s' =>
      assert (wc == -1) s!"rewritevaraddr(std): expected wc=-1, got {wc}"
      assert (s' == expectedSlice) s!"rewritevaraddr(std): unexpected slice (bits={s'.bitsRemaining})"
  | a, b => throw (IO.userError s!"rewritevaraddr(std): unexpected stack values {a.pretty}, {b.pretty}")

  -- Var address: rewrites the first bits even when address isn't 256-bit.
  let varAddr : BitString := #[false, false, true, true, false, true, false] -- 7 bits
  let varCell : Cell := mkMsgAddrVar_rewriteVarAddr anycast 0 varAddr
  let expectedVarBits : BitString := pfx ++ varAddr.drop pfx.size
  let expectedVarSlice : Slice := Slice.ofCell (Cell.mkOrdinary expectedVarBits #[])
  let (code1, st1) ← runRewriteVarAddr (Slice.ofCell varCell)
  assert (code1 == -1) s!"rewritevaraddr(var): unexpected exitCode={code1}"
  assert (st1.stack.size == 2) s!"rewritevaraddr(var): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num wc), .slice s' =>
      assert (wc == 0) s!"rewritevaraddr(var): expected wc=0, got {wc}"
      assert (s' == expectedVarSlice) s!"rewritevaraddr(var): unexpected slice (bits={s'.bitsRemaining})"
  | a, b => throw (IO.userError s!"rewritevaraddr(var): unexpected stack values {a.pretty}, {b.pretty}")

  -- Failure: anycast prefix longer than address (depth 6, addr_len 5) -> throws cellUnd.
  let pfx6 : BitString := #[true, true, true, true, true, true]
  let anycast6 := mkAnycastJustBits_rewriteVarAddr 6 pfx6
  let shortAddr : BitString := #[true, false, true, false, true] -- 5 bits
  let shortVar : Cell := mkMsgAddrVar_rewriteVarAddr anycast6 0 shortAddr
  let (code2, _st2) ← runRewriteVarAddr (Slice.ofCell shortVar)
  assert (code2 == (~~~ Excno.cellUnd.toInt)) s!"rewritevaraddr(prefix-too-long): expected cellUnd, got exitCode={code2}"

initialize
  Tests.registerTest "address/rewritevaraddr" testRewriteVarAddr
  Tests.registerRoundtrip (.tonEnvOp (.rewriteVarAddr false))
