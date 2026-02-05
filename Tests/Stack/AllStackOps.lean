import Tests.Stack.Util

open TvmLean Tests
open Tests.Stack

namespace Tests.Stack

def fetchFromTop (s : Stack) (idxFromTop : Nat) : Except String Value := do
  if idxFromTop < s.size then
    let pos := s.size - 1 - idxFromTop
    return s[pos]!
  else
    throw s!"stkUnd(fetch {idxFromTop})"

def swapFromTop (s : Stack) (iFromTop jFromTop : Nat) : Except String Stack := do
  let need := Nat.max iFromTop jFromTop
  if need < s.size then
    let pi := s.size - 1 - iFromTop
    let pj := s.size - 1 - jFromTop
    let vi := s[pi]!
    let vj := s[pj]!
    return (s.set! pi vj).set! pj vi
  else
    throw s!"stkUnd(swap {iFromTop},{jFromTop})"

def pop (s : Stack) : Except String (Value × Stack) := do
  if h : 0 < s.size then
    return (s.back (h := h), s.pop)
  else
    throw "stkUnd(pop)"

def popNat (s : Stack) : Except String (Nat × Stack) := do
  let (v, s') ← pop s
  match v with
  | .int (.num n) =>
      if n < 0 then throw "rangeChk(popNat<0)"
      return (n.toNat, s')
  | .int .nan => throw "rangeChk(popNat NaN)"
  | _ => throw "typeChk(popNat)"

def simulateBlkSwap (s : Stack) (x y : Nat) : Except String Stack := do
  let total := x + y
  if total ≤ s.size then
    let n := s.size
    let front := s.take (n - total)
    let below := s.extract (n - total) (n - y)
    let top := s.extract (n - y) n
    return front ++ top ++ below
  else
    throw "stkUnd(blkSwap)"

def simulateReverse (s : Stack) (x y : Nat) : Except String Stack := do
  let total := x + y
  if total ≤ s.size then
    let n := s.size
    let front := s.take (n - total)
    let revPart := (s.extract (n - total) (n - y)).reverse
    let top := s.extract (n - y) n
    return front ++ revPart ++ top
  else
    throw "stkUnd(reverse)"

def simulateFlowBlkdrop (s : Stack) (n : Nat) : Except String Stack := do
  if n ≤ s.size then
    return s.take (s.size - n)
  else
    throw "stkUnd(blkdrop)"

def simulateFlowBlkdrop2 (s : Stack) (x y : Nat) : Except String Stack := do
  let total := x + y
  if total ≤ s.size then
    let keepBottom := s.size - total
    let bottom := s.take keepBottom
    let top := s.extract (keepBottom + x) s.size
    return bottom ++ top
  else
    throw "stkUnd(blkdrop2)"

def simulateInstr (i : Instr) (stackIn : Stack) : Except String Stack := do
  match i with
  | .nop => return stackIn
  | .push idx =>
      let v ← fetchFromTop stackIn idx
      return stackIn.push v
  | .pop idx =>
      let s1 ← swapFromTop stackIn 0 idx
      let (_v, s2) ← pop s1
      return s2
  | .xchg0 idx =>
      swapFromTop stackIn 0 idx
  | .xchg1 idx =>
      swapFromTop stackIn 1 idx
  | .xchg x y =>
      if x = 0 ∨ y ≤ x then
        throw "invOpcode(xchg)"
      swapFromTop stackIn x y
  | .xchg2 x y =>
      let s1 ← swapFromTop stackIn 1 x
      swapFromTop s1 0 y
  | .xchg3 x y z =>
      let s1 ← swapFromTop stackIn 2 x
      let s2 ← swapFromTop s1 1 y
      swapFromTop s2 0 z
  | .xcpu x y =>
      let s1 ← swapFromTop stackIn 0 x
      let v ← fetchFromTop s1 y
      return s1.push v
  | .xc2pu x y z =>
      let s1 ← swapFromTop stackIn 1 x
      let s2 ← swapFromTop s1 0 y
      let v ← fetchFromTop s2 z
      return s2.push v
  | .xcpuxc x y z =>
      -- Mirrors `execInstrStackXcpuxc` (Stack/Xcpuxc.lean).
      if ¬(stackIn.size > Nat.max (Nat.max x y) 1 ∧ z ≤ stackIn.size) then
        throw "stkUnd(xcpuxc)"
      let s1 ← swapFromTop stackIn 1 x
      let v ← fetchFromTop s1 y
      let s2 := s1.push v
      let s3 ← swapFromTop s2 0 1
      swapFromTop s3 0 z
  | .xcpu2 x y z =>
      let s1 ← swapFromTop stackIn 0 x
      let v1 ← fetchFromTop s1 y
      let s2 := s1.push v1
      let v2 ← fetchFromTop s2 (z + 1)
      return s2.push v2
  | .puxc2 x y z =>
      let v ← fetchFromTop stackIn x
      let s1 := stackIn.push v
      let s2 ← swapFromTop s1 0 2
      let s3 ← swapFromTop s2 1 y
      swapFromTop s3 0 z
  | .puxc x y =>
      let v ← fetchFromTop stackIn x
      let s1 := stackIn.push v
      let s2 ← swapFromTop s1 0 1
      swapFromTop s2 0 y
  | .puxcpu x y z =>
      let v ← fetchFromTop stackIn x
      let s1 := stackIn.push v
      let s2 ← swapFromTop s1 0 1
      let s3 ← swapFromTop s2 0 y
      let v2 ← fetchFromTop s3 z
      return s3.push v2
  | .pu2xc x y z =>
      let v1 ← fetchFromTop stackIn x
      let s1 := stackIn.push v1
      let s2 ← swapFromTop s1 0 1
      let v2 ← fetchFromTop s2 y
      let s3 := s2.push v2
      let s4 ← swapFromTop s3 0 1
      swapFromTop s4 0 z
  | .push2 x y =>
      let v1 ← fetchFromTop stackIn x
      let s1 := stackIn.push v1
      let v2 ← fetchFromTop s1 (y + 1)
      return s1.push v2
  | .push3 x y z =>
      let v1 ← fetchFromTop stackIn x
      let s1 := stackIn.push v1
      let v2 ← fetchFromTop s1 (y + 1)
      let s2 := s1.push v2
      let v3 ← fetchFromTop s2 (z + 2)
      return s2.push v3
  | .blkSwap x y =>
      simulateBlkSwap stackIn x y
  | .blkPush x y =>
      if y < stackIn.size then
        let mut s := stackIn
        for _ in [0:x] do
          let v ← fetchFromTop s y
          s := s.push v
        return s
      else
        throw "stkUnd(blkPush)"
  | .rot =>
      let s1 ← swapFromTop stackIn 1 2
      swapFromTop s1 0 1
  | .rotRev =>
      let s1 ← swapFromTop stackIn 0 1
      swapFromTop s1 1 2
  | .twoSwap =>
      let s1 ← swapFromTop stackIn 1 3
      swapFromTop s1 0 2
  | .twoDup =>
      let v1 ← fetchFromTop stackIn 1
      let s1 := stackIn.push v1
      let v2 ← fetchFromTop s1 1
      return s1.push v2
  | .twoOver =>
      let v1 ← fetchFromTop stackIn 3
      let s1 := stackIn.push v1
      let v2 ← fetchFromTop s1 3
      return s1.push v2
  | .reverse x y =>
      -- This constructor reverses only the `x` segment immediately below the top `y` items.
      if x + y ≤ stackIn.size then
        let n := stackIn.size
        let front := stackIn.take (n - (x + y))
        let revPart := (stackIn.extract (n - (x + y)) (n - y)).reverse
        let top := stackIn.extract (n - y) n
        return front ++ revPart ++ top
      else
        throw "stkUnd(reverse imm)"
  | .pick =>
      let (x, s1) ← popNat stackIn
      let v ← fetchFromTop s1 x
      return s1.push v
  | .roll =>
      let (x, s1) ← popNat stackIn
      if x < s1.size then
        let mut s := s1
        for i in [0:x] do
          let k := x - 1 - i
          s ← swapFromTop s k (k + 1)
        return s
      else
        throw "stkUnd(roll)"
  | .rollRev =>
      let (x, s1) ← popNat stackIn
      if x < s1.size then
        let mut s := s1
        for i in [0:x] do
          s ← swapFromTop s i (i + 1)
        return s
      else
        throw "stkUnd(rollRev)"
  | .blkSwapX =>
      let (y, s1) ← popNat stackIn
      let (x, s2) ← popNat s1
      simulateBlkSwap s2 x y
  | .reverseX =>
      let (y, s1) ← popNat stackIn
      let (x, s2) ← popNat s1
      simulateReverse s2 x y
  | .dropX =>
      let (x, s1) ← popNat stackIn
      simulateFlowBlkdrop s1 x
  | .tuck =>
      let s1 ← swapFromTop stackIn 0 1
      let v ← fetchFromTop s1 1
      return s1.push v
  | .xchgX =>
      let (x, s1) ← popNat stackIn
      swapFromTop s1 0 x
  | .depth =>
      return stackIn.push (.int (.num (Int.ofNat stackIn.size)))
  | .chkDepth =>
      let (x, s1) ← popNat stackIn
      if x ≤ s1.size then return s1 else throw "stkUnd(chkDepth)"
  | .onlyTopX =>
      let (x, s1) ← popNat stackIn
      if x ≤ s1.size then
        let n := s1.size
        return s1.extract (n - x) n
      else
        throw "stkUnd(onlyTopX)"
  | .onlyX =>
      let (x, s1) ← popNat stackIn
      if x ≤ s1.size then return s1.take x else throw "stkUnd(onlyX)"
  | .drop2 =>
      simulateFlowBlkdrop stackIn 2
  | .blkdrop n =>
      simulateFlowBlkdrop stackIn n
  | .blkdrop2 x y =>
      simulateFlowBlkdrop2 stackIn x y
  | _ =>
      throw s!"simulateInstr: non-stack instr {i.pretty}"

def decodeInstrBits (bs : BitString) : Except String Instr := do
  let cell : Cell := Cell.mkOrdinary bs #[]
  let s := Slice.ofCell cell
  match decodeCp0 s with
  | .error e => throw s!"decodeCp0 failed: {reprStr e}"
  | .ok (i, rest) =>
      if rest.bitsRemaining != 0 then
        throw s!"decodeCp0 did not consume all bits: remaining={rest.bitsRemaining}"
      return i

def runCase (label : String) (i : Instr) (stackIn : Stack) : IO Unit := do
  let expected ←
    match simulateInstr i stackIn with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{label}: simulate failed: {e}")
  let (code, st) ← runInstrWithStack i stackIn
  assert (code == -1) s!"{label}: unexpected exitCode={code}"
  assertStackEq label st.stack expected

def testAllStackOps : IO Unit := do
  let decodeOrThrow (label : String) (bs : BitString) : IO Instr := do
    match decodeInstrBits bs with
    | .ok i => pure i
    | .error e => throw (IO.userError s!"{label} decode failed: {e}")

  -- Basic aliases / short forms
  runCase "NOP" .nop #[vInt 1, vInt 2]
  runCase "SWAP" (.xchg0 1) #[vInt 1, vInt 2]
  runCase "DUP" (.push 0) #[vInt 1, vInt 2]
  runCase "OVER" (.push 1) #[vInt 1, vInt 2]
  runCase "DROP" (.pop 0) #[vInt 1, vInt 2]
  runCase "NIP" (.pop 1) #[vInt 1, vInt 2, vInt 3]

  runCase "ROT" .rot #[vInt 1, vInt 2, vInt 3]
  runCase "ROTREV" .rotRev #[vInt 1, vInt 2, vInt 3]

  runCase "PICK" .pick #[vInt 10, vInt 11, vInt 12, vInt 2]
  runCase "ROLL" .roll #[vInt 1, vInt 2, vInt 3, vInt 4, vInt 2]
  runCase "ROLLREV" .rollRev #[vInt 1, vInt 2, vInt 3, vInt 4, vInt 2]

  runCase "BLKSWX" .blkSwapX #[vInt 10, vInt 11, vInt 12, vInt 13, vInt 2, vInt 1]
  runCase "REVX" .reverseX #[vInt 10, vInt 11, vInt 12, vInt 13, vInt 14, vInt 3, vInt 1]
  runCase "DROPX" .dropX #[vInt 1, vInt 2, vInt 3, vInt 2]
  runCase "TUCK" .tuck #[vInt 1, vInt 2]
  runCase "XCHGX" .xchgX #[vInt 1, vInt 2, vInt 3, vInt 1]
  runCase "DEPTH" .depth #[vInt 1, vInt 2, vInt 3]
  runCase "CHKDEPTH" .chkDepth #[vInt 1, vInt 2, vInt 3, vInt 2]
  runCase "ONLYTOPX" .onlyTopX #[vInt 1, vInt 2, vInt 3, vInt 2]
  runCase "ONLYX" .onlyX #[vInt 1, vInt 2, vInt 3, vInt 2]

  -- Immediate forms
  runCase "BLKDROP" (.blkdrop 2) #[vInt 1, vInt 2, vInt 3]
  runCase "BLKDROP2" (.blkdrop2 2 1) #[vInt 1, vInt 2, vInt 3, vInt 4, vInt 5]
  runCase "2DROP" .drop2 #[vInt 1, vInt 2, vInt 3]
  runCase "2SWAP" .twoSwap #[vInt 1, vInt 2, vInt 3, vInt 4]
  runCase "2DUP" .twoDup #[vInt 1, vInt 2]
  runCase "2OVER" .twoOver #[vInt 1, vInt 2, vInt 3, vInt 4]

  -- Parameterized stack permutations
  runCase "XCHG_0I" (.xchg0 15) (Array.range 20 |>.map (fun n => vInt (Int.ofNat n)))
  runCase "XCHG_1I" (.xchg1 2) #[vInt 1, vInt 2, vInt 3]
  runCase "XCHG_IJ" (.xchg 1 3) #[vInt 1, vInt 2, vInt 3, vInt 4]
  runCase "XCHG2" (.xchg2 2 3) #[vInt 1, vInt 2, vInt 3, vInt 4]
  runCase "XCHG3" (.xchg3 3 4 5) (Array.range 8 |>.map (fun n => vInt (Int.ofNat n)))

  runCase "PUSH2" (.push2 1 2) #[vInt 1, vInt 2, vInt 3, vInt 4]
  runCase "PUSH3" (.push3 0 1 2) #[vInt 1, vInt 2, vInt 3, vInt 4]
  runCase "BLKSWAP" (.blkSwap 2 1) #[vInt 10, vInt 11, vInt 12, vInt 13]
  runCase "REVERSE" (.reverse 3 1) #[vInt 10, vInt 11, vInt 12, vInt 13, vInt 14]
  runCase "BLKPUSH" (.blkPush 3 1) #[vInt 10, vInt 11, vInt 12]

  runCase "XCPU" (.xcpu 2 1) #[vInt 1, vInt 2, vInt 3, vInt 4]
  runCase "XC2PU" (.xc2pu 2 1 0) #[vInt 1, vInt 2, vInt 3, vInt 4]
  runCase "XCPU2" (.xcpu2 2 0 1) #[vInt 1, vInt 2, vInt 3, vInt 4]
  runCase "XCPUXC" (.xcpuxc 3 2 5) #[vInt 1, vInt 2, vInt 3, vInt 4, vInt 5]
  runCase "PUXC" (.puxc 2 2) #[vInt 1, vInt 2, vInt 3, vInt 4]
  runCase "PUXC2" (.puxc2 3 2 2) #[vInt 1, vInt 2, vInt 3, vInt 4]
  runCase "PUXCPU" (.puxcpu 2 2 1) #[vInt 1, vInt 2, vInt 3, vInt 4]
  runCase "PU2XC" (.pu2xc 2 1 2) #[vInt 1, vInt 2, vInt 3, vInt 4]

  -- Decode coverage for alternative encodings / long forms (spec has separate instruction names).
  let iPushLong ← decodeOrThrow "PUSH_LONG" (natToBits (0x56 * 256 + 200) 16)
  assert (iPushLong == .push 200) s!"PUSH_LONG decode mismatch: {iPushLong.pretty}"
  runCase "PUSH_LONG(exec)" iPushLong (Array.range 210 |>.map (fun n => vInt (Int.ofNat n)))

  let iPopLong ← decodeOrThrow "POP_LONG" (natToBits (0x57 * 256 + 200) 16)
  assert (iPopLong == .pop 200) s!"POP_LONG decode mismatch: {iPopLong.pretty}"
  runCase "POP_LONG(exec)" iPopLong (Array.range 210 |>.map (fun n => vInt (Int.ofNat n)))

  let iXchg0Long ← decodeOrThrow "XCHG_0I_LONG" (natToBits (0x11 * 256 + 200) 16)
  assert (iXchg0Long == .xchg0 200) s!"XCHG_0I_LONG decode mismatch: {iXchg0Long.pretty}"
  runCase "XCHG_0I_LONG(exec)" iXchg0Long (Array.range 210 |>.map (fun n => vInt (Int.ofNat n)))

  -- XCHG3_ALT is a distinct 24-bit encoding of XCHG3.
  let word24 : Nat := (0x540 <<< 12) + ((3 <<< 8) + (4 <<< 4) + 5)
  let iXchg3Alt ← decodeOrThrow "XCHG3_ALT" (natToBits word24 24)
  assert (iXchg3Alt == .xchg3 3 4 5) s!"XCHG3_ALT decode mismatch: {iXchg3Alt.pretty}"
  runCase "XCHG3_ALT(exec)" iXchg3Alt (Array.range 8 |>.map (fun n => vInt (Int.ofNat n)))

initialize
  Tests.registerTest "stack/all" testAllStackOps

  -- Roundtrips for canonical encodings.
  Tests.registerRoundtrip .nop
  Tests.registerRoundtrip (.xchg0 1)
  Tests.registerRoundtrip (.push 0)
  Tests.registerRoundtrip (.push 1)
  Tests.registerRoundtrip (.pop 0)
  Tests.registerRoundtrip (.pop 1)
  Tests.registerRoundtrip .rot
  Tests.registerRoundtrip .rotRev
  Tests.registerRoundtrip .pick
  Tests.registerRoundtrip .roll
  Tests.registerRoundtrip .rollRev
  Tests.registerRoundtrip .blkSwapX
  Tests.registerRoundtrip .reverseX
  Tests.registerRoundtrip .dropX
  Tests.registerRoundtrip .tuck
  Tests.registerRoundtrip .xchgX
  Tests.registerRoundtrip .depth
  Tests.registerRoundtrip .chkDepth
  Tests.registerRoundtrip .onlyTopX
  Tests.registerRoundtrip .onlyX
  Tests.registerRoundtrip (.blkdrop 2)
  Tests.registerRoundtrip (.blkdrop2 2 1)
  Tests.registerRoundtrip .drop2
  Tests.registerRoundtrip .twoSwap
  Tests.registerRoundtrip .twoDup
  Tests.registerRoundtrip .twoOver
  Tests.registerRoundtrip (.xchg0 15)
  Tests.registerRoundtrip (.xchg1 2)
  Tests.registerRoundtrip (.xchg 1 3)
  Tests.registerRoundtrip (.xchg2 2 3)
  Tests.registerRoundtrip (.xchg3 3 4 5)
  Tests.registerRoundtrip (.push2 1 2)
  Tests.registerRoundtrip (.push3 0 1 2)
  Tests.registerRoundtrip (.blkSwap 2 1)
  Tests.registerRoundtrip (.reverse 3 1)
  Tests.registerRoundtrip (.blkPush 3 1)
  Tests.registerRoundtrip (.xcpu 2 1)
  Tests.registerRoundtrip (.xc2pu 2 1 0)
  Tests.registerRoundtrip (.xcpu2 2 0 1)
  Tests.registerRoundtrip (.xcpuxc 3 2 5)
  Tests.registerRoundtrip (.puxc 2 2)
  Tests.registerRoundtrip (.puxc2 3 2 2)
  Tests.registerRoundtrip (.puxcpu 2 2 1)
  Tests.registerRoundtrip (.pu2xc 2 1 2)

end Tests.Stack
