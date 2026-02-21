import TvmLean.Model

namespace TvmLean

inductive TypedVal where
  | int (i : IntVal)
  | cell (c : Cell)
  | slice (s : Slice)
  | builder (b : Builder)
  | tuple (t : Array Value)
  | cont (k : Continuation)
  | null
  deriving Repr

def TypedVal.toValue : TypedVal → Value
  | .int i => .int i
  | .cell c => .cell c
  | .slice s => .slice s
  | .builder b => .builder b
  | .tuple t => .tuple t
  | .cont k => .cont k
  | .null => .null

def TypedVal.ofValue : Value → TypedVal
  | .int i => .int i
  | .cell c => .cell c
  | .slice s => .slice s
  | .builder b => .builder b
  | .tuple t => .tuple t
  | .cont k => .cont k
  | .null => .null

def TypedVal.asInt? : TypedVal → Option IntVal
  | .int i => some i
  | _ => none

def TypedVal.asCell? : TypedVal → Option Cell
  | .cell c => some c
  | _ => none

def TypedVal.asSlice? : TypedVal → Option Slice
  | .slice s => some s
  | _ => none

def TypedVal.asBuilder? : TypedVal → Option Builder
  | .builder b => some b
  | _ => none

@[simp] theorem typedVal_toValue_ofValue (v : Value) :
    TypedVal.toValue (TypedVal.ofValue v) = v := by
  cases v <;> rfl

@[simp] theorem typedVal_ofValue_toValue (v : TypedVal) :
    TypedVal.ofValue (TypedVal.toValue v) = v := by
  cases v <;> rfl

@[simp] theorem typedVal_asInt?_int (i : IntVal) :
    TypedVal.asInt? (.int i) = some i := by
  rfl

@[simp] theorem typedVal_asCell?_cell (c : Cell) :
    TypedVal.asCell? (.cell c) = some c := by
  rfl

@[simp] theorem typedVal_asSlice?_slice (s : Slice) :
    TypedVal.asSlice? (.slice s) = some s := by
  rfl

@[simp] theorem typedVal_asBuilder?_builder (b : Builder) :
    TypedVal.asBuilder? (.builder b) = some b := by
  rfl

abbrev StackView := List TypedVal

namespace StackView

def empty : StackView := []

def push (v : TypedVal) (view : StackView) : StackView :=
  v :: view

def pop? : StackView → Option (TypedVal × StackView)
  | [] => none
  | v :: rest => some (v, rest)

def toStack : StackView → Stack
  | [] => #[]
  | v :: rest => (toStack rest).push v.toValue

def ofStack (stack : Stack) : StackView :=
  stack.foldl (fun acc v => TypedVal.ofValue v :: acc) []

@[simp] theorem toStack_nil :
    toStack ([] : StackView) = #[] := by
  rfl

@[simp] theorem toStack_cons (v : TypedVal) (rest : StackView) :
    toStack (v :: rest) = (toStack rest).push v.toValue := by
  rfl

@[simp] theorem push_eq_cons (v : TypedVal) (view : StackView) :
    push v view = v :: view := by
  rfl

@[simp] theorem pop?_nil :
    pop? ([] : StackView) = none := by
  rfl

@[simp] theorem pop?_cons (v : TypedVal) (rest : StackView) :
    pop? (v :: rest) = some (v, rest) := by
  rfl

@[simp] theorem ofStack_empty :
    ofStack (#[] : Stack) = [] := by
  simp [ofStack]

end StackView

def VmState.withStackView (st : VmState) (view : StackView) : VmState :=
  { st with stack := view.toStack }

def VmState.stackView (st : VmState) : StackView :=
  StackView.ofStack st.stack

@[simp] theorem vmState_withStackView_stack (st : VmState) (view : StackView) :
    (st.withStackView view).stack = view.toStack := by
  rfl

@[simp] theorem vmState_withStackView_regs (st : VmState) (view : StackView) :
    (st.withStackView view).regs = st.regs := by
  rfl

@[simp] theorem vmState_withStackView_cc (st : VmState) (view : StackView) :
    (st.withStackView view).cc = st.cc := by
  rfl

@[simp] theorem vmState_withStackView_cp (st : VmState) (view : StackView) :
    (st.withStackView view).cp = st.cp := by
  rfl

@[simp] theorem vmState_withStackView_gas (st : VmState) (view : StackView) :
    (st.withStackView view).gas = st.gas := by
  rfl

end TvmLean
