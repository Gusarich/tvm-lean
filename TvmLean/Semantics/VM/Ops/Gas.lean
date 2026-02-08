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

end TvmLean
