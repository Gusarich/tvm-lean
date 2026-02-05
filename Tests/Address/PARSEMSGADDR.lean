-- Auto-generated stub for TVM instruction PARSEMSGADDR (category: address).
import Tests.Registry

open TvmLean Tests

def mkAnycastNothingBits_parseMsgAddr : BitString := #[false]

def mkAnycastJustBits_parseMsgAddr (depth : Nat) (pfx : BitString) : BitString :=
  #[true] ++ natToBits depth (natLenBits 30) ++ pfx

def mkMsgAddrNone_parseMsgAddr : Cell :=
  Cell.mkOrdinary (natToBits 0 2) #[]

def mkMsgAddrExtern_parseMsgAddr (addr : BitString) : Cell :=
  Cell.mkOrdinary (natToBits 1 2 ++ natToBits addr.size 9 ++ addr) #[]

def mkMsgAddrStd_parseMsgAddr (anycast : BitString) (workchain : Int) (addr256 : BitString) : Cell :=
  let wcBits :=
    match intToBitsTwos workchain 8 with
    | .ok bs => bs
    | .error _ => #[]
  Cell.mkOrdinary (natToBits 2 2 ++ anycast ++ wcBits ++ addr256) #[]

def mkMsgAddrVar_parseMsgAddr (anycast : BitString) (workchain : Int) (addr : BitString) : Cell :=
  let wcBits :=
    match intToBitsTwos workchain 32 with
    | .ok bs => bs
    | .error _ => #[]
  Cell.mkOrdinary (natToBits 3 2 ++ anycast ++ natToBits addr.size 9 ++ wcBits ++ addr) #[]

def runParseMsgAddr (s : Slice) (fuel : Nat := 50) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [.tonEnvOp (.parseMsgAddr false)] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := #[.slice s] }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError "parsemsgaddr: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def testParseMsgAddr : IO Unit := do
  -- addr_none$00 -> (0)
  let (code0, st0) ← runParseMsgAddr (Slice.ofCell mkMsgAddrNone_parseMsgAddr)
  assert (code0 == -1) s!"parsemsgaddr(addr_none): unexpected exitCode={code0}"
  assert (st0.stack.size == 1) s!"parsemsgaddr(addr_none): unexpected stack size={st0.stack.size}"
  let expected0 : Value := .tuple #[.int (.num 0)]
  assert (st0.stack[0]! == expected0) s!"parsemsgaddr(addr_none): unexpected tuple {st0.stack[0]!.pretty}"

  -- addr_extern$01 -> (1, addr_bits)
  let extBits : BitString := #[true, false, true]
  let (code1, st1) ← runParseMsgAddr (Slice.ofCell (mkMsgAddrExtern_parseMsgAddr extBits))
  assert (code1 == -1) s!"parsemsgaddr(addr_extern): unexpected exitCode={code1}"
  assert (st1.stack.size == 1) s!"parsemsgaddr(addr_extern): unexpected stack size={st1.stack.size}"
  let expected1 : Value := .tuple #[.int (.num 1), .slice (Slice.ofCell (Cell.mkOrdinary extBits #[]))]
  assert (st1.stack[0]! == expected1) s!"parsemsgaddr(addr_extern): unexpected tuple {st1.stack[0]!.pretty}"

  -- addr_std$10, no anycast -> (2, null, wc:int8, addr256)
  let addrBytesA : Array UInt8 := Array.replicate 32 0xaa
  let addrBitsA : BitString := (cellOfBytes addrBytesA).bits
  let stdA : Cell := mkMsgAddrStd_parseMsgAddr mkAnycastNothingBits_parseMsgAddr (-1) addrBitsA
  let (code2, st2) ← runParseMsgAddr (Slice.ofCell stdA)
  assert (code2 == -1) s!"parsemsgaddr(addr_std): unexpected exitCode={code2}"
  assert (st2.stack.size == 1) s!"parsemsgaddr(addr_std): unexpected stack size={st2.stack.size}"
  let expected2 : Value :=
    .tuple #[.int (.num 2), .null, .int (.num (-1)), .slice (Slice.ofCell (cellOfBytes addrBytesA))]
  assert (st2.stack[0]! == expected2) s!"parsemsgaddr(addr_std): unexpected tuple {st2.stack[0]!.pretty}"

  -- addr_std$10, with anycast -> returns prefix slice.
  let pfx : BitString := #[true, false, true, false, true] -- depth=5
  let anycast := mkAnycastJustBits_parseMsgAddr 5 pfx
  let addrBytesB : Array UInt8 := Array.replicate 32 0x55
  let addrBitsB : BitString := (cellOfBytes addrBytesB).bits
  let stdB : Cell := mkMsgAddrStd_parseMsgAddr anycast 0 addrBitsB
  let (code3, st3) ← runParseMsgAddr (Slice.ofCell stdB)
  assert (code3 == -1) s!"parsemsgaddr(anycast): unexpected exitCode={code3}"
  assert (st3.stack.size == 1) s!"parsemsgaddr(anycast): unexpected stack size={st3.stack.size}"
  let expected3 : Value :=
    .tuple
      #[ .int (.num 2)
        , .slice (Slice.ofCell (Cell.mkOrdinary pfx #[]))
        , .int (.num 0)
        , .slice (Slice.ofCell (cellOfBytes addrBytesB)) ]
  assert (st3.stack[0]! == expected3) s!"parsemsgaddr(anycast): unexpected tuple {st3.stack[0]!.pretty}"

  -- addr_var$11 -> (3, anycast_or_null, wc:int32, addr_bits)
  let varAddr : BitString := #[true, true, false, false, true, false, true] -- 7 bits
  let varC : Cell := mkMsgAddrVar_parseMsgAddr mkAnycastNothingBits_parseMsgAddr (-2) varAddr
  let (code4, st4) ← runParseMsgAddr (Slice.ofCell varC)
  assert (code4 == -1) s!"parsemsgaddr(addr_var): unexpected exitCode={code4}"
  assert (st4.stack.size == 1) s!"parsemsgaddr(addr_var): unexpected stack size={st4.stack.size}"
  let expected4 : Value :=
    .tuple #[.int (.num 3), .null, .int (.num (-2)), .slice (Slice.ofCell (Cell.mkOrdinary varAddr #[]))]
  assert (st4.stack[0]! == expected4) s!"parsemsgaddr(addr_var): unexpected tuple {st4.stack[0]!.pretty}"

  -- Trailing bits after a valid address: throws cellUnd (requires empty_ext()).
  let badBits := stdA.bits ++ #[true]
  let badCell : Cell := Cell.mkOrdinary badBits #[]
  let (code5, _st5) ← runParseMsgAddr (Slice.ofCell badCell)
  assert (code5 == (~~~ Excno.cellUnd.toInt)) s!"parsemsgaddr(trailing): expected cellUnd, got exitCode={code5}"

initialize
  Tests.registerTest "address/parsemsgaddr" testParseMsgAddr
  Tests.registerRoundtrip (.tonEnvOp (.parseMsgAddr false))
