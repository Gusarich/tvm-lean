import TvmLean.Model
import TvmLean.Semantics.VM.Monad

namespace TvmLean

def VmState.consumeGas (st : VmState) (amount : Int) : VmState :=
  { st with gas := st.gas.consume amount }

def VmState.registerChkSgnCall (st : VmState) : VmState :=
  let cnt := st.chksgnCounter + 1
  let st' := { st with chksgnCounter := cnt }
  if cnt > chksgnFreeCount then
    st'.consumeGas chksgnGasPrice
  else
    st'

def VmState.consumeTupleGas (st : VmState) (tupleLen : Nat) : VmState :=
  st.consumeGas (Int.ofNat tupleLen * tupleEntryGasPrice)

def VmState.consumeStackGas (st : VmState) (stackDepth : Nat) : VmState :=
  let extra : Nat := if stackDepth > freeStackDepth then stackDepth - freeStackDepth else 0
  st.consumeGas (Int.ofNat extra * stackEntryGasPrice)

def VmState.registerCellLoad (st : VmState) (c : Cell) : VmState :=
  let h : Array UInt8 := Cell.hashBytes c
  let seen : Bool := st.loadedCells.any (fun x => x == h)
  let st' : VmState :=
    if seen then
      st
    else
      { st with loadedCells := st.loadedCells.push h }
  st'.consumeGas (if seen then cellReloadGasPrice else cellLoadGasPrice)

/-- VM-monad cell load: registers the cell, consumes gas, and throws `.outOfGas`
    if gas goes negative.  This mirrors C++ `load_cell_slice_impl` →
    `register_cell_load` → `consume_gas` → `consume_chk` (global_version ≥ 4)
    which immediately throws `VmNoGas` on gas exhaustion, aborting the instruction. -/
def VM.registerCellLoad (c : Cell) : VM Unit := do
  modify fun st => st.registerCellLoad c
  let st ← get
  if decide (st.gas.gasRemaining < 0) then
    throw .outOfGas

end TvmLean
