import TvmLean.Proof.Stack
import TvmLean.Semantics.Exec.Dispatch
import TvmLean.Semantics.Exec.Cont.PushCtr
import TvmLean.Semantics.Exec.Cont.PopCtr
import TvmLean.Semantics.Exec.Cell.Ctos
import TvmLean.Semantics.Exec.Cell.Ldu
import TvmLean.Semantics.Exec.Stack.Pop
import TvmLean.Semantics.Exec.Arith.Inc
import TvmLean.Semantics.Exec.Stack.PushInt
import TvmLean.Semantics.Exec.Arith.Ext
import TvmLean.Semantics.Exec.Cell.Newc
import TvmLean.Semantics.Exec.Cell.Stu
import TvmLean.Semantics.Exec.Cell.Endc
import TvmLean.Semantics.Exec.Flow.If
import TvmLean.Semantics.VM.Ops.Stack
import TvmLean.Semantics.VM.Ops.State

namespace TvmLean

def execInstrSpecCore (i : Instr) : VM Unit :=
  match i with
  | .pushCtr idx =>
      execInstrContPushCtr (.pushCtr idx) (pure ())
  | .popCtr idx =>
      execInstrContPopCtr (.popCtr idx) (pure ())
  | .ctos =>
      execInstrCellCtos .ctos (pure ())
  | .ldu bits =>
      execInstrCellLdu (.ldu bits) (pure ())
  | .pop idx =>
      execInstrStackPop (.pop idx) (pure ())
  | .inc =>
      execInstrArithInc .inc (pure ())
  | .pushInt n =>
      execInstrStackPushInt (.pushInt n) (pure ())
  | .arithExt op =>
      execInstrArithExt (.arithExt op) (pure ())
  | .newc =>
      execInstrCellNewc .newc (pure ())
  | .stu bits =>
      execInstrCellStu (.stu bits) (pure ())
  | .endc =>
      execInstrCellEndc .endc (pure ())
  | .if_ =>
      execInstrFlowIf .if_ (pure ())
  | i =>
      VM.unimplementedInstr { name := Instr.pretty i } "proof spec core: unsupported opcode"

@[simp] theorem execInstr_pushCtr_eq (host : Host) (idx : Nat) :
    execInstr host (.pushCtr idx) = execInstrSpecCore (.pushCtr idx) := by
  rfl

@[simp] theorem execInstr_popCtr_eq (host : Host) (idx : Nat) :
    execInstr host (.popCtr idx) = execInstrSpecCore (.popCtr idx) := by
  rfl

@[simp] theorem execInstr_ctos_eq (host : Host) :
    execInstr host .ctos = execInstrSpecCore .ctos := by
  rfl

@[simp] theorem execInstr_ldu_eq (host : Host) (bits : Nat) :
    execInstr host (.ldu bits) = execInstrSpecCore (.ldu bits) := by
  rfl

@[simp] theorem execInstr_pop_eq (host : Host) (idx : Nat) :
    execInstr host (.pop idx) = execInstrSpecCore (.pop idx) := by
  rfl

@[simp] theorem execInstr_inc_eq (host : Host) :
    execInstr host .inc = execInstrSpecCore .inc := by
  rfl

@[simp] theorem execInstr_pushInt_eq (host : Host) (n : IntVal) :
    execInstr host (.pushInt n) = execInstrSpecCore (.pushInt n) := by
  rfl

@[simp] theorem execInstr_arithExt_eq (host : Host) (op : ArithExtInstr) :
    execInstr host (.arithExt op) = execInstrSpecCore (.arithExt op) := by
  rfl

@[simp] theorem execInstr_newc_eq (host : Host) :
    execInstr host .newc = execInstrSpecCore .newc := by
  rfl

@[simp] theorem execInstr_stu_eq (host : Host) (bits : Nat) :
    execInstr host (.stu bits) = execInstrSpecCore (.stu bits) := by
  rfl

@[simp] theorem execInstr_endc_eq (host : Host) :
    execInstr host .endc = execInstrSpecCore .endc := by
  rfl

@[simp] theorem execInstr_if_eq (host : Host) :
    execInstr host .if_ = execInstrSpecCore .if_ := by
  rfl

theorem instr_pushCtr4_run (host : Host) (st : VmState) :
    (execInstr host (.pushCtr 4)).run st =
      (.ok (), { st with stack := st.stack.push (.cell st.regs.c4) }) := by
  simp [execInstrSpecCore, execInstrContPushCtr, VM.push, VmState.getCtr, ExceptT.run]
  rfl

theorem instr_newc_run (host : Host) (st : VmState) :
    (execInstr host .newc).run st =
      (.ok (), { st with stack := st.stack.push (.builder Builder.empty) }) := by
  simp [execInstrSpecCore, execInstrCellNewc, VM.push, ExceptT.run]
  rfl

theorem instr_if_false_run (host : Host) (st : VmState) :
    (execInstr host .if_).run { st with stack := #[.int (.num 0), .cont (.quit 0)] } =
      (.ok (), { st with stack := #[] }) := by
  simp [execInstrSpecCore, execInstrFlowIf, VM.checkUnderflow, VM.popCont, VM.popBool, VM.popInt, ExceptT.run]
  rfl

theorem instrSpec_if_false_run (st : VmState) :
    (execInstrSpecCore .if_).run { st with stack := #[.int (.num 0), .cont (.quit 0)] } =
      (.ok (), { st with stack := #[] }) := by
  simp [execInstrSpecCore, execInstrFlowIf, VM.checkUnderflow, VM.popCont, VM.popBool, VM.popInt, ExceptT.run]
  rfl

theorem instrSpec_if_false_run_consumed (st : VmState) (g : Int) :
    (execInstrSpecCore .if_).run ({ st with stack := #[.int (.num 0), .cont (.quit 0)] }.consumeGas g) =
      (.ok (), { ({ st with stack := #[.int (.num 0), .cont (.quit 0)] }.consumeGas g) with stack := #[] }) := by
  simp [execInstrSpecCore, execInstrFlowIf, VM.checkUnderflow, VM.popCont, VM.popBool, VM.popInt, ExceptT.run]
  rfl

end TvmLean
