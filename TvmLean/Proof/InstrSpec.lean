import TvmLean.Proof.Stack
import TvmLean.Semantics.Exec.Dispatch
import TvmLean.Semantics.Exec.Cont.PushCtr
import TvmLean.Semantics.Exec.Cont.PopCtr
import TvmLean.Semantics.Exec.Cell.Ctos
import TvmLean.Semantics.Exec.Cell.Ldu
import TvmLean.Semantics.Exec.Cell.LoadInt
import TvmLean.Semantics.Exec.Cell.LoadSliceFixed
import TvmLean.Semantics.Exec.Cell.LoadSliceX
import TvmLean.Semantics.Exec.Stack.Push
import TvmLean.Semantics.Exec.Stack.PushPow2
import TvmLean.Semantics.Exec.Stack.PushPow2Dec
import TvmLean.Semantics.Exec.Stack.PushNegPow2
import TvmLean.Semantics.Exec.Stack.Pop
import TvmLean.Semantics.Exec.Stack.Xchg
import TvmLean.Semantics.Exec.Stack.Xchg0
import TvmLean.Semantics.Exec.Stack.Xchg1
import TvmLean.Semantics.Exec.Stack.Xchg2
import TvmLean.Semantics.Exec.Stack.Xchg3
import TvmLean.Semantics.Exec.Arith.Inc
import TvmLean.Semantics.Exec.Arith.Dec
import TvmLean.Semantics.Exec.Arith.Negate
import TvmLean.Semantics.Exec.Arith.Add
import TvmLean.Semantics.Exec.Arith.Sub
import TvmLean.Semantics.Exec.Arith.Mul
import TvmLean.Semantics.Exec.Arith.Lshift
import TvmLean.Semantics.Exec.Arith.Rshift
import TvmLean.Semantics.Exec.Arith.LshiftConst
import TvmLean.Semantics.Exec.Arith.RshiftConst
import TvmLean.Semantics.Exec.Stack.PushInt
import TvmLean.Semantics.Exec.Arith.Ext
import TvmLean.Semantics.Exec.Cell.Newc
import TvmLean.Semantics.Exec.Cell.Sti
import TvmLean.Semantics.Exec.Cell.Stref
import TvmLean.Semantics.Exec.Cell.Stu
import TvmLean.Semantics.Exec.Cell.Endc
import TvmLean.Semantics.Exec.Flow.If
import TvmLean.Semantics.Exec.Flow.Ifnot
import TvmLean.Semantics.Exec.Flow.Ifjmp
import TvmLean.Semantics.Exec.Flow.Ifnotjmp
import TvmLean.Semantics.Exec.Flow.Ifret
import TvmLean.Semantics.Exec.Flow.Ifnotret
import TvmLean.Semantics.Exec.Flow.CallRef
import TvmLean.Semantics.Exec.Flow.JmpRef
import TvmLean.Semantics.Exec.Flow.CallDict
import TvmLean.Semantics.Exec.Flow.Until
import TvmLean.Semantics.Exec.Flow.While
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
  | .loadInt unsigned prefetch quiet bits =>
      execInstrCellLoadInt (.loadInt unsigned prefetch quiet bits) (pure ())
  | .loadSliceFixed prefetch quiet bits =>
      execInstrCellLoadSliceFixed (.loadSliceFixed prefetch quiet bits) (pure ())
  | .loadSliceX prefetch quiet =>
      execInstrCellLoadSliceX (.loadSliceX prefetch quiet) (pure ())
  | .push idx =>
      execInstrStackPush (.push idx) (pure ())
  | .xchg0 idx =>
      execInstrStackXchg0 (.xchg0 idx) (pure ())
  | .xchg1 idx =>
      execInstrStackXchg1 (.xchg1 idx) (pure ())
  | .xchg x y =>
      execInstrStackXchg (.xchg x y) (pure ())
  | .xchg2 x y =>
      execInstrStackXchg2 (.xchg2 x y) (pure ())
  | .xchg3 x y z =>
      execInstrStackXchg3 (.xchg3 x y z) (pure ())
  | .pop idx =>
      execInstrStackPop (.pop idx) (pure ())
  | .add =>
      execInstrArithAdd .add (pure ())
  | .sub =>
      execInstrArithSub .sub (pure ())
  | .mul =>
      execInstrArithMul .mul (pure ())
  | .negate =>
      execInstrArithNegate .negate (pure ())
  | .inc =>
      execInstrArithInc .inc (pure ())
  | .dec =>
      execInstrArithDec .dec (pure ())
  | .pushInt n =>
      execInstrStackPushInt (.pushInt n) (pure ())
  | .pushPow2 exp =>
      execInstrStackPushPow2 (.pushPow2 exp) (pure ())
  | .pushPow2Dec exp =>
      execInstrStackPushPow2Dec (.pushPow2Dec exp) (pure ())
  | .pushNegPow2 exp =>
      execInstrStackPushNegPow2 (.pushNegPow2 exp) (pure ())
  | .arithExt op =>
      execInstrArithExt (.arithExt op) (pure ())
  | .lshift =>
      execInstrArithLshift .lshift (pure ())
  | .rshift =>
      execInstrArithRshift .rshift (pure ())
  | .lshiftConst quiet bits =>
      execInstrArithLshiftConst (.lshiftConst quiet bits) (pure ())
  | .rshiftConst quiet bits =>
      execInstrArithRshiftConst (.rshiftConst quiet bits) (pure ())
  | .newc =>
      execInstrCellNewc .newc (pure ())
  | .sti bits =>
      execInstrCellSti (.sti bits) (pure ())
  | .stu bits =>
      execInstrCellStu (.stu bits) (pure ())
  | .stref =>
      execInstrCellStref .stref (pure ())
  | .endc =>
      execInstrCellEndc .endc (pure ())
  | .if_ =>
      execInstrFlowIf .if_ (pure ())
  | .ifnot =>
      execInstrFlowIfnot .ifnot (pure ())
  | .ifjmp =>
      execInstrFlowIfjmp .ifjmp (pure ())
  | .ifnotjmp =>
      execInstrFlowIfnotjmp .ifnotjmp (pure ())
  | .ifret =>
      execInstrFlowIfret .ifret (pure ())
  | .ifnotret =>
      execInstrFlowIfnotret .ifnotret (pure ())
  | .callRef code =>
      execInstrFlowCallRef (.callRef code) (pure ())
  | .jmpRef code =>
      execInstrFlowJmpRef (.jmpRef code) (pure ())
  | .callDict idx =>
      execInstrFlowCallDict (.callDict idx) (pure ())
  | .until =>
      execInstrFlowUntil .until (pure ())
  | .while_ =>
      execInstrFlowWhile .while_ (pure ())
  | i =>
      VM.unimplementedInstr { name := Instr.pretty i } "proof spec core: unsupported opcode"

@[simp] theorem execInstrSpecCore_pushCtr (idx : Nat) :
    execInstrSpecCore (.pushCtr idx) = execInstrContPushCtr (.pushCtr idx) (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_popCtr (idx : Nat) :
    execInstrSpecCore (.popCtr idx) = execInstrContPopCtr (.popCtr idx) (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_push (idx : Nat) :
    execInstrSpecCore (.push idx) = execInstrStackPush (.push idx) (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_pop (idx : Nat) :
    execInstrSpecCore (.pop idx) = execInstrStackPop (.pop idx) (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_xchg0 (idx : Nat) :
    execInstrSpecCore (.xchg0 idx) = execInstrStackXchg0 (.xchg0 idx) (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_xchg1 (idx : Nat) :
    execInstrSpecCore (.xchg1 idx) = execInstrStackXchg1 (.xchg1 idx) (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_xchg2 (x y : Nat) :
    execInstrSpecCore (.xchg2 x y) = execInstrStackXchg2 (.xchg2 x y) (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_add :
    execInstrSpecCore .add = execInstrArithAdd .add (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_dec :
    execInstrSpecCore .dec = execInstrArithDec .dec (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_newc :
    execInstrSpecCore .newc = execInstrCellNewc .newc (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_if :
    execInstrSpecCore .if_ = execInstrFlowIf .if_ (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_ifnot :
    execInstrSpecCore .ifnot = execInstrFlowIfnot .ifnot (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_ifjmp :
    execInstrSpecCore .ifjmp = execInstrFlowIfjmp .ifjmp (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_ifnotjmp :
    execInstrSpecCore .ifnotjmp = execInstrFlowIfnotjmp .ifnotjmp (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_ifret :
    execInstrSpecCore .ifret = execInstrFlowIfret .ifret (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_ifnotret :
    execInstrSpecCore .ifnotret = execInstrFlowIfnotret .ifnotret (pure ()) := by
  rfl

@[simp] theorem execInstrSpecCore_while :
    execInstrSpecCore .while_ = execInstrFlowWhile .while_ (pure ()) := by
  rfl

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

@[simp] theorem execInstr_loadInt_eq (host : Host) (unsigned prefetch quiet : Bool) (bits : Nat) :
    execInstr host (.loadInt unsigned prefetch quiet bits) =
      execInstrSpecCore (.loadInt unsigned prefetch quiet bits) := by
  rfl

@[simp] theorem execInstr_loadSliceFixed_eq (host : Host) (prefetch quiet : Bool) (bits : Nat) :
    execInstr host (.loadSliceFixed prefetch quiet bits) =
      execInstrSpecCore (.loadSliceFixed prefetch quiet bits) := by
  rfl

@[simp] theorem execInstr_loadSliceX_eq (host : Host) (prefetch quiet : Bool) :
    execInstr host (.loadSliceX prefetch quiet) =
      execInstrSpecCore (.loadSliceX prefetch quiet) := by
  rfl

@[simp] theorem execInstr_push_eq (host : Host) (idx : Nat) :
    execInstr host (.push idx) = execInstrSpecCore (.push idx) := by
  rfl

@[simp] theorem execInstr_xchg0_eq (host : Host) (idx : Nat) :
    execInstr host (.xchg0 idx) = execInstrSpecCore (.xchg0 idx) := by
  rfl

@[simp] theorem execInstr_xchg1_eq (host : Host) (idx : Nat) :
    execInstr host (.xchg1 idx) = execInstrSpecCore (.xchg1 idx) := by
  rfl

@[simp] theorem execInstr_xchg_eq (host : Host) (x y : Nat) :
    execInstr host (.xchg x y) = execInstrSpecCore (.xchg x y) := by
  rfl

@[simp] theorem execInstr_xchg2_eq (host : Host) (x y : Nat) :
    execInstr host (.xchg2 x y) = execInstrSpecCore (.xchg2 x y) := by
  rfl

@[simp] theorem execInstr_xchg3_eq (host : Host) (x y z : Nat) :
    execInstr host (.xchg3 x y z) = execInstrSpecCore (.xchg3 x y z) := by
  rfl

@[simp] theorem execInstr_pop_eq (host : Host) (idx : Nat) :
    execInstr host (.pop idx) = execInstrSpecCore (.pop idx) := by
  rfl

@[simp] theorem execInstr_pop_long_eq (host : Host) (idx : Nat) :
    execInstr host (.pop idx) = execInstrSpecCore (.pop idx) := by
  exact execInstr_pop_eq host idx

@[simp] theorem execInstr_add_eq (host : Host) :
    execInstr host .add = execInstrSpecCore .add := by
  rfl

@[simp] theorem execInstr_sub_eq (host : Host) :
    execInstr host .sub = execInstrSpecCore .sub := by
  rfl

@[simp] theorem execInstr_mul_eq (host : Host) :
    execInstr host .mul = execInstrSpecCore .mul := by
  rfl

@[simp] theorem execInstr_negate_eq (host : Host) :
    execInstr host .negate = execInstrSpecCore .negate := by
  rfl

@[simp] theorem execInstr_inc_eq (host : Host) :
    execInstr host .inc = execInstrSpecCore .inc := by
  rfl

@[simp] theorem execInstr_dec_eq (host : Host) :
    execInstr host .dec = execInstrSpecCore .dec := by
  rfl

@[simp] theorem execInstr_pushInt_eq (host : Host) (n : IntVal) :
    execInstr host (.pushInt n) = execInstrSpecCore (.pushInt n) := by
  rfl

@[simp] theorem execInstr_pushPow2_eq (host : Host) (exp : Nat) :
    execInstr host (.pushPow2 exp) = execInstrSpecCore (.pushPow2 exp) := by
  rfl

@[simp] theorem execInstr_pushPow2Dec_eq (host : Host) (exp : Nat) :
    execInstr host (.pushPow2Dec exp) = execInstrSpecCore (.pushPow2Dec exp) := by
  rfl

@[simp] theorem execInstr_pushNegPow2_eq (host : Host) (exp : Nat) :
    execInstr host (.pushNegPow2 exp) = execInstrSpecCore (.pushNegPow2 exp) := by
  rfl

@[simp] theorem execInstr_arithExt_eq (host : Host) (op : ArithExtInstr) :
    execInstr host (.arithExt op) = execInstrSpecCore (.arithExt op) := by
  rfl

@[simp] theorem execInstr_lshift_eq (host : Host) :
    execInstr host .lshift = execInstrSpecCore .lshift := by
  rfl

@[simp] theorem execInstr_rshift_eq (host : Host) :
    execInstr host .rshift = execInstrSpecCore .rshift := by
  rfl

@[simp] theorem execInstr_lshiftConst_eq (host : Host) (quiet : Bool) (bits : Nat) :
    execInstr host (.lshiftConst quiet bits) = execInstrSpecCore (.lshiftConst quiet bits) := by
  rfl

@[simp] theorem execInstr_rshiftConst_eq (host : Host) (quiet : Bool) (bits : Nat) :
    execInstr host (.rshiftConst quiet bits) = execInstrSpecCore (.rshiftConst quiet bits) := by
  rfl

@[simp] theorem execInstr_newc_eq (host : Host) :
    execInstr host .newc = execInstrSpecCore .newc := by
  rfl

@[simp] theorem execInstr_sti_eq (host : Host) (bits : Nat) :
    execInstr host (.sti bits) = execInstrSpecCore (.sti bits) := by
  rfl

@[simp] theorem execInstr_stu_eq (host : Host) (bits : Nat) :
    execInstr host (.stu bits) = execInstrSpecCore (.stu bits) := by
  rfl

@[simp] theorem execInstr_stref_eq (host : Host) :
    execInstr host .stref = execInstrSpecCore .stref := by
  rfl

@[simp] theorem execInstr_endc_eq (host : Host) :
    execInstr host .endc = execInstrSpecCore .endc := by
  rfl

@[simp] theorem execInstr_if_eq (host : Host) :
    execInstr host .if_ = execInstrSpecCore .if_ := by
  rfl

@[simp] theorem execInstr_ifnot_eq (host : Host) :
    execInstr host .ifnot = execInstrSpecCore .ifnot := by
  rfl

@[simp] theorem execInstr_ifjmp_eq (host : Host) :
    execInstr host .ifjmp = execInstrSpecCore .ifjmp := by
  rfl

@[simp] theorem execInstr_ifnotjmp_eq (host : Host) :
    execInstr host .ifnotjmp = execInstrSpecCore .ifnotjmp := by
  rfl

@[simp] theorem execInstr_ifret_eq (host : Host) :
    execInstr host .ifret = execInstrSpecCore .ifret := by
  rfl

@[simp] theorem execInstr_ifnotret_eq (host : Host) :
    execInstr host .ifnotret = execInstrSpecCore .ifnotret := by
  rfl

@[simp] theorem execInstr_callRef_eq (host : Host) (code : Slice) :
    execInstr host (.callRef code) = execInstrSpecCore (.callRef code) := by
  rfl

@[simp] theorem execInstr_jmpRef_eq (host : Host) (code : Slice) :
    execInstr host (.jmpRef code) = execInstrSpecCore (.jmpRef code) := by
  rfl

@[simp] theorem execInstr_callDict_eq (host : Host) (idx : Nat) :
    execInstr host (.callDict idx) = execInstrSpecCore (.callDict idx) := by
  rfl

@[simp] theorem execInstr_until_eq (host : Host) :
    execInstr host .until = execInstrSpecCore .until := by
  rfl

@[simp] theorem execInstr_while_eq (host : Host) :
    execInstr host .while_ = execInstrSpecCore .while_ := by
  rfl

@[simp] theorem execInstr_dup_eq (host : Host) :
    execInstr host (.push 0) = execInstrSpecCore (.push 0) := by
  exact execInstr_push_eq host 0

@[simp] theorem execInstr_over_eq (host : Host) :
    execInstr host (.push 1) = execInstrSpecCore (.push 1) := by
  exact execInstr_push_eq host 1

@[simp] theorem execInstr_swap_eq (host : Host) :
    execInstr host (.xchg0 1) = execInstrSpecCore (.xchg0 1) := by
  exact execInstr_xchg0_eq host 1

@[simp] theorem execInstr_drop_eq (host : Host) :
    execInstr host (.pop 0) = execInstrSpecCore (.pop 0) := by
  exact execInstr_pop_eq host 0

@[simp] theorem execInstr_nip_eq (host : Host) :
    execInstr host (.pop 1) = execInstrSpecCore (.pop 1) := by
  exact execInstr_pop_eq host 1

theorem instr_pushCtr4_run (host : Host) (st : VmState) :
    (((execInstr host (.pushCtr 4)).run st) : Except Excno Unit × VmState) =
      ((.ok () : Except Excno Unit), { st with stack := st.stack.push (.cell st.regs.c4) }) := by
  simp only [execInstr_pushCtr_eq, execInstrSpecCore_pushCtr, execInstrContPushCtr, VM.push, VmState.getCtr,
    ExceptT.run]
  rfl

theorem instr_swap_run (host : Host) (st : VmState) :
    (execInstr host (.xchg0 1)).run { st with stack := #[.int (.num 2), .int (.num 7)] } =
      ((.ok () : Except Excno Unit), { st with stack := #[.int (.num 7), .int (.num 2)] }) := by
  simp only [execInstr_swap_eq, execInstrSpecCore_xchg0, execInstrStackXchg0, VM.swap, ExceptT.run]
  rfl

theorem instr_xchg1_run (host : Host) (st : VmState) :
    (execInstr host (.xchg1 2)).run { st with stack := #[.int (.num 2), .int (.num 7), .int (.num 9)] } =
      ((.ok () : Except Excno Unit), { st with stack := #[.int (.num 7), .int (.num 2), .int (.num 9)] }) := by
  simp only [execInstr_xchg1_eq, execInstrSpecCore_xchg1, execInstrStackXchg1, VM.swap, ExceptT.run]
  rfl

theorem instr_xchg2_run (host : Host) (st : VmState) :
    (execInstr host (.xchg2 2 3)).run
      { st with stack := #[.int (.num 1), .int (.num 2), .int (.num 3), .int (.num 4)] } =
      ((.ok () : Except Excno Unit), { st with stack := #[.int (.num 4), .int (.num 3), .int (.num 2), .int (.num 1)] }) := by
  simp only [execInstr_xchg2_eq, execInstrSpecCore_xchg2, execInstrStackXchg2, VM.swap, ExceptT.run]
  rfl

theorem instr_dup_run (host : Host) (st : VmState) :
    (execInstr host (.push 0)).run { st with stack := #[.int (.num 7)] } =
      ((.ok () : Except Excno Unit), { st with stack := #[.int (.num 7), .int (.num 7)] }) := by
  simp only [execInstr_dup_eq, execInstrSpecCore_push, execInstrStackPush, VM.fetch, VM.push, ExceptT.run]
  rfl

theorem instr_nip_run (host : Host) (st : VmState) :
    (execInstr host (.pop 1)).run { st with stack := #[.int (.num 2), .int (.num 7)] } =
      ((.ok () : Except Excno Unit), { st with stack := #[.int (.num 7)] }) := by
  simp only [execInstr_nip_eq, execInstrSpecCore_pop, execInstrStackPop, VM.swap, VM.pop, ExceptT.run]
  rfl

theorem instr_add_underflow_run (host : Host) (st : VmState) :
    (execInstr host .add).run { st with stack := #[] } =
      ((.error .stkUnd : Except Excno Unit), { st with stack := #[] }) := by
  simp only [execInstr_add_eq, execInstrSpecCore_add, execInstrArithAdd, VM.checkUnderflow, ExceptT.run]
  rfl

theorem instr_dec_nan_run (host : Host) (st : VmState) :
    (execInstr host .dec).run { st with stack := #[.int .nan] } =
      ((.error .intOv : Except Excno Unit), { st with stack := #[] }) := by
  simp only [execInstr_dec_eq, execInstrSpecCore_dec, execInstrArithDec, VM.popInt, VM.pop, VM.pushIntQuiet,
    IntVal.dec, IntVal.sub, ExceptT.run]
  rfl

theorem instr_dec_underflow_run (host : Host) (st : VmState) :
    (execInstr host .dec).run { st with stack := #[] } =
      ((.error .stkUnd : Except Excno Unit), { st with stack := #[] }) := by
  simp only [execInstr_dec_eq, execInstrSpecCore_dec, execInstrArithDec, VM.popInt, VM.pop, ExceptT.run]
  rfl

@[simp] theorem execInstr_modpow2_const_eq
    (host : Host) (roundMode : Int) (quiet : Bool) (bits : Nat) :
    execInstr host (.arithExt (.shrMod false false 2 roundMode quiet (some bits))) =
      execInstrSpecCore (.arithExt (.shrMod false false 2 roundMode quiet (some bits))) := by
  exact execInstr_arithExt_eq host (.shrMod false false 2 roundMode quiet (some bits))

theorem instr_newc_run (host : Host) (st : VmState) :
    (execInstr host .newc).run st =
      ((.ok () : Except Excno Unit), { st with stack := st.stack.push (.builder Builder.empty) }) := by
  simp only [execInstr_newc_eq, execInstrSpecCore_newc, execInstrCellNewc, VM.push, ExceptT.run]
  rfl

theorem instr_popCtr4_run (host : Host) (st : VmState) (c : Cell) :
    (execInstr host (.popCtr 4)).run { st with stack := #[.cell c] } =
      ((.ok () : Except Excno Unit), { st with regs := { st.regs with c4 := c }, stack := #[] }) := by
  simp only [execInstr_popCtr_eq, execInstrSpecCore_popCtr, execInstrContPopCtr, VM.pop, VmState.setCtr, ExceptT.run]
  rfl

theorem instr_popCtr0_run (host : Host) (st : VmState) (k : Continuation) :
    (execInstr host (.popCtr 0)).run { st with stack := #[.cont k] } =
      ((.ok () : Except Excno Unit), { st with regs := { st.regs with c0 := k }, stack := #[] }) := by
  simp only [execInstr_popCtr_eq, execInstrSpecCore_popCtr, execInstrContPopCtr, VM.pop, VmState.setCtr, ExceptT.run]
  rfl

theorem instr_popCtr4_typeChk_run (host : Host) (st : VmState) (n : Int) :
    (execInstr host (.popCtr 4)).run { st with stack := #[.int (.num n)] } =
      ((.error .typeChk : Except Excno Unit), { st with stack := #[] }) := by
  simp only [execInstr_popCtr_eq, execInstrSpecCore_popCtr, execInstrContPopCtr, VM.pop, VmState.setCtr, ExceptT.run]
  rfl

theorem instr_popCtr6_typeChk_run (host : Host) (st : VmState) (v : Value) :
    (execInstr host (.popCtr 6)).run { st with stack := #[v] } =
      ((.error .typeChk : Except Excno Unit), { st with stack := #[] }) := by
  simp only [execInstr_popCtr_eq, execInstrSpecCore_popCtr, execInstrContPopCtr, VM.pop, VmState.setCtr, ExceptT.run]
  rfl

theorem instr_if_run_bool (host : Host) (st : VmState) (cont : Continuation) (b : Bool) :
    (execInstr host .if_).run { st with stack := #[.int (.num (if b then 1 else 0)), .cont cont] } =
      if b then
        (execInstr host .if_).run { st with stack := #[.int (.num 1), .cont cont] }
      else
        (execInstr host .if_).run { st with stack := #[.int (.num 0), .cont cont] } := by
  cases b <;> rfl

theorem instr_ifnot_run_bool (host : Host) (st : VmState) (cont : Continuation) (b : Bool) :
    (execInstr host .ifnot).run { st with stack := #[.int (.num (if b then 1 else 0)), .cont cont] } =
      if b then
        (execInstr host .ifnot).run { st with stack := #[.int (.num 1), .cont cont] }
      else
        (execInstr host .ifnot).run { st with stack := #[.int (.num 0), .cont cont] } := by
  cases b <;> rfl

theorem instr_ifjmp_run_bool (host : Host) (st : VmState) (cont : Continuation) (b : Bool) :
    (execInstr host .ifjmp).run { st with stack := #[.int (.num (if b then 1 else 0)), .cont cont] } =
      if b then
        (execInstr host .ifjmp).run { st with stack := #[.int (.num 1), .cont cont] }
      else
        (execInstr host .ifjmp).run { st with stack := #[.int (.num 0), .cont cont] } := by
  cases b <;> simp

theorem instr_ifnotjmp_run_bool (host : Host) (st : VmState) (cont : Continuation) (b : Bool) :
    (execInstr host .ifnotjmp).run { st with stack := #[.int (.num (if b then 1 else 0)), .cont cont] } =
      if b then
        (execInstr host .ifnotjmp).run { st with stack := #[.int (.num 1), .cont cont] }
      else
        (execInstr host .ifnotjmp).run { st with stack := #[.int (.num 0), .cont cont] } := by
  cases b <;> simp

theorem instr_if_ifnot_branch_norm_quit (host : Host) (st : VmState) (n : Int) (b : Bool) :
    (execInstr host (if b then .if_ else .ifnot)).run
      { st with stack := #[.int (.num (if b then 1 else 0)), .cont (.quit n)] } =
      if b then
        (execInstr host .if_).run { st with stack := #[.int (.num 1), .cont (.quit n)] }
      else
        (execInstr host .ifnot).run { st with stack := #[.int (.num 0), .cont (.quit n)] } := by
  cases b <;> rfl

theorem instr_ifjmp_ifnotjmp_branch_norm_quit (host : Host) (st : VmState) (n : Int) (b : Bool) :
    (execInstr host (if b then .ifjmp else .ifnotjmp)).run
      { st with stack := #[.int (.num (if b then 1 else 0)), .cont (.quit n)] } =
      if b then
        (execInstr host .ifjmp).run { st with stack := #[.int (.num 1), .cont (.quit n)] }
      else
        (execInstr host .ifnotjmp).run { st with stack := #[.int (.num 0), .cont (.quit n)] } := by
  cases b <;> simp

theorem instr_ifret_run_bool (host : Host) (st : VmState) (b : Bool) :
    (execInstr host .ifret).run { st with stack := #[.int (.num (if b then 1 else 0))] } =
      if b then
        (execInstr host .ifret).run { st with stack := #[.int (.num 1)] }
      else
        (execInstr host .ifret).run { st with stack := #[.int (.num 0)] } := by
  cases b <;> rfl

theorem instr_ifnotret_run_bool (host : Host) (st : VmState) (b : Bool) :
    (execInstr host .ifnotret).run { st with stack := #[.int (.num (if b then 1 else 0))] } =
      if b then
        (execInstr host .ifnotret).run { st with stack := #[.int (.num 1)] }
      else
        (execInstr host .ifnotret).run { st with stack := #[.int (.num 0)] } := by
  cases b <;> rfl

theorem instr_if_false_run (host : Host) (st : VmState) :
    (execInstr host .if_).run { st with stack := #[.int (.num 0), .cont (.quit 0)] } =
      ((.ok () : Except Excno Unit), { st with stack := #[] }) := by
  simp only [execInstr_if_eq, execInstrSpecCore_if, execInstrFlowIf, VM.checkUnderflow, VM.popCont, VM.popBool,
    VM.popInt, ExceptT.run]
  rfl

theorem instr_ifnot_false_run (host : Host) (st : VmState) :
    (execInstr host .ifnot).run { st with stack := #[.int (.num 1), .cont (.quit 0)] } =
      ((.ok () : Except Excno Unit), { st with stack := #[] }) := by
  simp only [execInstr_ifnot_eq, execInstrSpecCore_ifnot, execInstrFlowIfnot, VM.checkUnderflow, VM.popCont,
    VM.popBool,
    VM.popInt, ExceptT.run]
  rfl

theorem instr_ifjmp_true_run (host : Host) (st : VmState) :
    (execInstr host .ifjmp).run { st with stack := #[.int (.num 1), .cont (.quit 7)] } =
      ((.ok () : Except Excno Unit), { st with stack := #[], cc := .quit 7 }) := by
  simp only [execInstr_ifjmp_eq, execInstrSpecCore_ifjmp, execInstrFlowIfjmp, VM.checkUnderflow, VM.popCont, VM.popBool,
    VM.popInt, VM.jump, ExceptT.run]
  rfl

theorem instr_ifnotjmp_false_run (host : Host) (st : VmState) :
    (execInstr host .ifnotjmp).run { st with stack := #[.int (.num 1), .cont (.quit 7)] } =
      ((.ok () : Except Excno Unit), { st with stack := #[] }) := by
  simp only [execInstr_ifnotjmp_eq, execInstrSpecCore_ifnotjmp, execInstrFlowIfnotjmp, VM.checkUnderflow, VM.popCont,
    VM.popBool, VM.popInt, ExceptT.run]
  rfl

theorem instr_ifret_true_run (host : Host) (st : VmState) :
    (execInstr host .ifret).run { st with regs := { st.regs with c0 := .quit 9 }, stack := #[.int (.num 1)] } =
      ((.ok () : Except Excno Unit), { st with regs := { st.regs with c0 := .quit 0 }, stack := #[], cc := .quit 9 }) := by
  simp only [execInstr_ifret_eq, execInstrSpecCore_ifret, execInstrFlowIfret, VM.popBool, VM.popInt, VM.ret, VM.jump,
    ExceptT.run]
  rfl

theorem instr_ifnotret_false_run (host : Host) (st : VmState) :
    (execInstr host .ifnotret).run { st with stack := #[.int (.num 1)] } =
      ((.ok () : Except Excno Unit), { st with stack := #[] }) := by
  simp only [execInstr_ifnotret_eq, execInstrSpecCore_ifnotret, execInstrFlowIfnotret, VM.popBool, VM.popInt,
    ExceptT.run]
  rfl

theorem instr_while_underflow_run (host : Host) (st : VmState) :
    (execInstr host .while_).run { st with stack := #[.cont (.quit 0)] } =
      ((.error .stkUnd : Except Excno Unit), { st with stack := #[.cont (.quit 0)] }) := by
  simp only [execInstr_while_eq, execInstrSpecCore_while, execInstrFlowWhile, VM.checkUnderflow, ExceptT.run]
  rfl

theorem instrSpec_if_false_run (st : VmState) :
    (execInstrSpecCore .if_).run { st with stack := #[.int (.num 0), .cont (.quit 0)] } =
      ((.ok () : Except Excno Unit), { st with stack := #[] }) := by
  simp only [execInstrSpecCore_if, execInstrFlowIf, VM.checkUnderflow, VM.popCont, VM.popBool, VM.popInt, ExceptT.run]
  rfl

theorem instrSpec_if_false_run_consumed (st : VmState) (g : Int) :
    (execInstrSpecCore .if_).run ({ st with stack := #[.int (.num 0), .cont (.quit 0)] }.consumeGas g) =
      ((.ok () : Except Excno Unit), { ({ st with stack := #[.int (.num 0), .cont (.quit 0)] }.consumeGas g) with stack := #[] }) := by
  simp only [execInstrSpecCore_if, execInstrFlowIf, VM.checkUnderflow, VM.popCont, VM.popBool, VM.popInt, ExceptT.run]
  rfl

end TvmLean
