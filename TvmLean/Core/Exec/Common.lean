import TvmLean.Core.Prelude

namespace TvmLean

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
  let st ← get
  if 0 < st.regs.c7.size then
    match st.regs.c7[0]! with
    | .tuple params =>
        match params.get? 14 with
        | some (.tuple unpacked) => return unpacked
        | some .null => throw .invOpcode
        | some _ => throw .typeChk
        | none => throw .invOpcode
    | _ => throw .typeChk
  else
    throw .typeChk

def VM.getMsgPrices (isMasterchain : Bool) : VM (Int × Int × Int × Nat × Nat) := do
  -- Mirrors `util::get_msg_prices(get_unpacked_config_tuple(st), is_masterchain)`.
  -- Returns (lump_price, bit_price, cell_price, ihr_factor, first_frac).
  let unpacked ← VM.getUnpackedConfigTuple
  let idx : Nat := if isMasterchain then 4 else 5
  match unpacked.get? idx with
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
  | some .null => throw .invOpcode
  | some _ => throw .typeChk
  | none => throw .typeChk

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

  match unpacked.get? idx with
  | some (.slice pricesCs) =>
      match (parseGasLimitsPrices pricesCs : Except Excno (Nat × Nat × Nat)) with
      | .ok (gasPrice, flatGasLimit, flatGasPrice) => return (gasPrice, flatGasLimit, flatGasPrice)
      | .error e => throw e
  | some .null => throw .invOpcode
  | some _ => throw .typeChk
  | none => throw .typeChk

end TvmLean
