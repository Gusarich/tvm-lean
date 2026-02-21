import TvmLean.Semantics

namespace TvmLean

@[simp] theorem vm_pure_run {α : Type} (a : α) (st : VmState) :
    ExceptT.run (pure a : VM α) st = (.ok a, st) := by
  rfl

@[simp] theorem vm_throw_run {α : Type} (e : Excno) (st : VmState) :
    ExceptT.run (throw e : VM α) st = (.error e, st) := by
  rfl

@[simp] theorem vm_get_run (st : VmState) :
    ExceptT.run (get : VM VmState) st = (.ok st, st) := by
  rfl

@[simp] theorem vm_modify_run (f : VmState → VmState) (st : VmState) :
    ExceptT.run (modify f : VM Unit) st = (.ok (), f st) := by
  rfl

@[simp] theorem vm_set_run (st st' : VmState) :
    ExceptT.run (set st' : VM Unit) st = (.ok (), st') := by
  rfl

@[simp] theorem vm_bind_run {α β : Type} (mx : VM α) (f : α → VM β) (st : VmState) :
    ExceptT.run (mx >>= f) st =
      match ExceptT.run mx st with
      | (.ok a, st') => ExceptT.run (f a) st'
      | (.error e, st') => (.error e, st') := by
  change StateT.run (ExceptT.run mx >>= ExceptT.bindCont f) st = _
  rw [StateT.run_bind]
  cases h : mx st with
  | mk res st' =>
      cases res with
      | ok a =>
          simp [ExceptT.run, StateT.run, h, ExceptT.bindCont, bind, Bind.bind]
      | error e =>
          simp [ExceptT.run, StateT.run, h, ExceptT.bindCont, bind, Bind.bind]
          rfl

theorem applyCregsCdata_empty (st : VmState) :
    st.applyCregsCdata OrdCregs.empty OrdCdata.empty = st := by
  simp [VmState.applyCregsCdata, OrdCregs.empty, OrdCdata.empty]

@[simp] theorem consumeGas_stack (st : VmState) (amount : Int) :
    (st.consumeGas amount).stack = st.stack := by
  rfl

@[simp] theorem consumeGas_regs (st : VmState) (amount : Int) :
    (st.consumeGas amount).regs = st.regs := by
  rfl

@[simp] theorem consumeGas_cc (st : VmState) (amount : Int) :
    (st.consumeGas amount).cc = st.cc := by
  rfl

@[simp] theorem consumeGas_cp (st : VmState) (amount : Int) :
    (st.consumeGas amount).cp = st.cp := by
  rfl

@[simp] theorem consumeGas_chksgnCounter (st : VmState) (amount : Int) :
    (st.consumeGas amount).chksgnCounter = st.chksgnCounter := by
  rfl

@[simp] theorem consumeGas_loadedCells (st : VmState) (amount : Int) :
    (st.consumeGas amount).loadedCells = st.loadedCells := by
  rfl

@[simp] theorem consumeGas_maxDataDepth (st : VmState) (amount : Int) :
    (st.consumeGas amount).maxDataDepth = st.maxDataDepth := by
  rfl

@[simp] theorem consumeGas_gasMax (st : VmState) (amount : Int) :
    (st.consumeGas amount).gas.gasMax = st.gas.gasMax := by
  simp [VmState.consumeGas, GasLimits.consume]

@[simp] theorem consumeGas_gasLimit (st : VmState) (amount : Int) :
    (st.consumeGas amount).gas.gasLimit = st.gas.gasLimit := by
  simp [VmState.consumeGas, GasLimits.consume]

@[simp] theorem consumeGas_gasCredit (st : VmState) (amount : Int) :
    (st.consumeGas amount).gas.gasCredit = st.gas.gasCredit := by
  simp [VmState.consumeGas, GasLimits.consume]

@[simp] theorem consumeGas_gasBase (st : VmState) (amount : Int) :
    (st.consumeGas amount).gas.gasBase = st.gas.gasBase := by
  simp [VmState.consumeGas, GasLimits.consume]

@[simp] theorem consumeGas_gasRemaining (st : VmState) (amount : Int) :
    (st.consumeGas amount).gas.gasRemaining = st.gas.gasRemaining - amount := by
  simp [VmState.consumeGas, GasLimits.consume]

@[simp] theorem registerCellLoad_cc (st : VmState) (c : Cell) :
    (st.registerCellLoad c).cc = st.cc := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas]

@[simp] theorem registerCellLoad_cp (st : VmState) (c : Cell) :
    (st.registerCellLoad c).cp = st.cp := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas]

@[simp] theorem registerCellLoad_regs (st : VmState) (c : Cell) :
    (st.registerCellLoad c).regs = st.regs := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas]

@[simp] theorem registerCellLoad_gasMax (st : VmState) (c : Cell) :
    (st.registerCellLoad c).gas.gasMax = st.gas.gasMax := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas, GasLimits.consume]

@[simp] theorem registerCellLoad_gasLimit (st : VmState) (c : Cell) :
    (st.registerCellLoad c).gas.gasLimit = st.gas.gasLimit := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas, GasLimits.consume]

@[simp] theorem registerCellLoad_gasCredit (st : VmState) (c : Cell) :
    (st.registerCellLoad c).gas.gasCredit = st.gas.gasCredit := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas, GasLimits.consume]

@[simp] theorem registerCellLoad_gasBase (st : VmState) (c : Cell) :
    (st.registerCellLoad c).gas.gasBase = st.gas.gasBase := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas, GasLimits.consume]

@[simp] theorem registerCellLoad_gasRemaining (st : VmState) (c : Cell) :
    (st.registerCellLoad c).gas.gasRemaining =
      st.gas.gasRemaining -
        (if st.loadedCells.any (fun x => x == Cell.hashBytes c) then cellReloadGasPrice else cellLoadGasPrice) := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas, GasLimits.consume]

@[simp] theorem registerCellLoad_maxDataDepth (st : VmState) (c : Cell) :
    (st.registerCellLoad c).maxDataDepth = st.maxDataDepth := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas]

@[simp] theorem tryCommit_regs (st : VmState) :
    (st.tryCommit).2.regs = st.regs := by
  unfold VmState.tryCommit
  by_cases h : st.regs.c4.depthLe st.maxDataDepth && st.regs.c5.depthLe st.maxDataDepth <;>
    simp [h]

end TvmLean
