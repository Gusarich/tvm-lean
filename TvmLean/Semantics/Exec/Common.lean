import TvmLean.Model
import TvmLean.Semantics.VM.Ops.Stack
import TvmLean.Semantics.VM.Ops.Cells
import TvmLean.Semantics.VM.Ops.Gas
import TvmLean.Semantics.VM.Ops.Cont
import TvmLean.Semantics.VM.Ops.State

namespace TvmLean

def VM.checkUnderflow (n : Nat) : VM Unit := do
  let st ← get
  if st.stack.size < n then
    throw .stkUnd

/--
Marks an instruction path as not yet implemented.

The VM core still uses `Excno` as the execution error channel, so this bridges the
structured `VmError.unimplemented` marker to `Excno.unimplemented`.
-/
def VM.unimplementedInstr (id : InstrId) (msg : String := "not yet implemented") : VM α := do
  let _ : VmError := .unimplemented id msg
  throw .unimplemented

def VM.execNullSwapIf (cond : Bool) (depth : Nat) (count : Nat) : VM Unit := do
  -- Matches C++ `exec_null_swap_if` / `exec_null_swap_if_many` (tupleops.cpp).
  let st ← get
  if depth + 1 > st.stack.size then
    throw .stkUnd
  let x ← VM.popIntFinite
  let trigger : Bool := if cond then x != 0 else x == 0
  if trigger then
    for _ in [0:count] do
      VM.push .null
    for i in [0:depth] do
      VM.swap i (i + count)
  VM.push (.int (.num x))

def VM.getUnpackedConfigTuple : VM (Array Value) := do
  -- Mirrors C++ `get_unpacked_config_tuple(st)` (tonops.cpp):
  --   t1 := tuple_index(c7, 0); t2 := tuple_index(t1, 14); return t2
  match (← get).regs.c7[0]? with
  | none => throw .rangeChk
  | some (Value.tuple params) =>
      match params[14]? with
      | none => throw .rangeChk
      | some (Value.tuple unpacked) => return unpacked
      | some _ => throw .typeChk
  | some _ =>
      throw .typeChk

def VM.getMsgPrices (isMasterchain : Bool) : VM (Int × Int × Int × Nat × Nat) := do
  -- Mirrors `util::get_msg_prices(get_unpacked_config_tuple(st), is_masterchain)`.
  -- Returns (lump_price, bit_price, cell_price, ihr_factor, first_frac).
  let unpacked ← VM.getUnpackedConfigTuple
  let idx : Nat := if isMasterchain then 4 else 5
  match unpacked[idx]? with
  | some (.slice pricesCs) =>
      let (tag, s1) ← pricesCs.takeBitsAsNatCellUnd 8
      if tag != 0xea then
        throw .cellUnd
      let (lumpPrice, s2) ← s1.takeBitsAsNatCellUnd 64
      let (bitPrice, s3) ← s2.takeBitsAsNatCellUnd 64
      let (cellPrice, s4) ← s3.takeBitsAsNatCellUnd 64
      let (ihrFactor, s5) ← s4.takeBitsAsNatCellUnd 32 -- ihr_price_factor
      let (firstFrac, s6) ← s5.takeBitsAsNatCellUnd 16
      let (_, _) ← s6.takeBitsAsNatCellUnd 16 -- next_frac
      return (Int.ofNat lumpPrice, Int.ofNat bitPrice, Int.ofNat cellPrice, ihrFactor, firstFrac)
  | some .null => throw .typeChk
  | some _ => throw .typeChk
  | none => throw .rangeChk

def VM.getGasPrices (isMasterchain : Bool) : VM (Nat × Nat × Nat) := do
  -- Mirrors `util::get_gas_prices(get_unpacked_config_tuple(st), is_masterchain)`.
  -- Returns (gas_price, flat_gas_limit, flat_gas_price).
  let unpacked ← VM.getUnpackedConfigTuple
  let idx : Nat := if isMasterchain then 2 else 3

  let parseTail (tag : Nat) (s : Slice) : Except Excno Nat := do
    if tag == 0xdd then
      let (gasPrice, s2) ← s.takeBitsAsNatCellUnd 64
      let (_, s3) ← s2.takeBitsAsNatCellUnd 64 -- gas_limit
      let (_, s4) ← s3.takeBitsAsNatCellUnd 64 -- gas_credit
      let (_, s5) ← s4.takeBitsAsNatCellUnd 64 -- block_gas_limit
      let (_, s6) ← s5.takeBitsAsNatCellUnd 64 -- freeze_due_limit
      let (_, _) ← s6.takeBitsAsNatCellUnd 64 -- delete_due_limit
      return gasPrice
    else if tag == 0xde then
      let (gasPrice, s2) ← s.takeBitsAsNatCellUnd 64
      let (_, s3) ← s2.takeBitsAsNatCellUnd 64 -- gas_limit
      let (_, s4) ← s3.takeBitsAsNatCellUnd 64 -- special_gas_limit
      let (_, s5) ← s4.takeBitsAsNatCellUnd 64 -- gas_credit
      let (_, s6) ← s5.takeBitsAsNatCellUnd 64 -- block_gas_limit
      let (_, s7) ← s6.takeBitsAsNatCellUnd 64 -- freeze_due_limit
      let (_, _) ← s7.takeBitsAsNatCellUnd 64 -- delete_due_limit
      return gasPrice
    else
      throw .cellUnd

  let parseGasLimitsPrices (cs : Slice) : Except Excno (Nat × Nat × Nat) := do
    let (tag0, s1) ← cs.takeBitsAsNatCellUnd 8
    if tag0 == 0xd1 then
      let (flatLimit, s2) ← s1.takeBitsAsNatCellUnd 64
      let (flatPrice, s3) ← s2.takeBitsAsNatCellUnd 64
      let (tag1, s4) ← s3.takeBitsAsNatCellUnd 8
      let gasPrice ← parseTail tag1 s4
      return (gasPrice, flatLimit, flatPrice)
    else
      let gasPrice ← parseTail tag0 s1
      return (gasPrice, 0, 0)

  match unpacked[idx]? with
  | some (.slice pricesCs) =>
      match (parseGasLimitsPrices pricesCs : Except Excno (Nat × Nat × Nat)) with
      | .ok (gasPrice, flatGasLimit, flatGasPrice) => return (gasPrice, flatGasLimit, flatGasPrice)
      | .error e => throw e
  | some .null => throw .typeChk
  | some _ => throw .typeChk
  | none => throw .rangeChk

def VM.extractCc (saveCr : Nat) (stackCopy : Int := -1) (ccArgs : Int := -1) : VM Continuation := do
  -- Mirrors C++ `VmState::extract_cc(save_cr, stack_copy, cc_args)`.
  let st ← get
  let codeAfter : Slice ←
    match st.cc with
    | .ordinary code _ _ _ => pure code
    | _ => throw .typeChk

  let depth : Nat := st.stack.size
  let mut bottom : Stack := #[]
  let mut newStack : Stack := st.stack

  if decide (stackCopy < 0) then
    -- Keep the whole stack, capture nothing.
    bottom := #[]
    newStack := st.stack
  else
    let copy : Nat := stackCopy.toNat
    if copy > depth then
      throw .stkUnd
    if copy = depth then
      bottom := #[]
      newStack := st.stack
    else if copy = 0 then
      bottom := st.stack
      newStack := #[]
    else
      let split : Nat := depth - copy
      bottom := st.stack.take split
      newStack := st.stack.extract split depth

  -- Update stack and charge stack gas only when we actually split off a non-empty `newStack` via `copy > 0`.
  -- This matches C++ behavior closely enough for our purposes.
  let st :=
    if decide (0 < stackCopy) && newStack.size > 0 then
      ({ st with stack := newStack }).consumeStackGas newStack.size
    else
      { st with stack := newStack }

  let mut ccCregs : OrdCregs := OrdCregs.empty
  let mut regs := st.regs
  if (saveCr &&& 1) = 1 then
    ccCregs := { ccCregs with c0 := some regs.c0 }
    regs := { regs with c0 := .quit 0 }
  if (saveCr &&& 2) = 2 then
    ccCregs := { ccCregs with c1 := some regs.c1 }
    regs := { regs with c1 := .quit 1 }
  if (saveCr &&& 4) = 4 then
    ccCregs := { ccCregs with c2 := some regs.c2 }

  set { st with regs := regs }

  let ccCdata : OrdCdata := { stack := bottom, nargs := ccArgs }
  return .ordinary codeAfter (.quit 0) ccCregs ccCdata

def VM.pushCode : VM Unit := do
  -- Mirrors C++ `VmState::push_code()`: push current remaining code slice.
  let st ← get
  match st.cc with
  | .ordinary code _ _ _ =>
      VM.push (.slice code)
  | _ =>
      throw .typeChk

end TvmLean
