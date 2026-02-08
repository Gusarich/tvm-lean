import TvmLean.Model.Instr.Ast

namespace TvmLean

mutual
  structure OrdCregs where
    -- Minimal continuation control regs for MVP diff-testing.
    -- TVM allows SETCONTCTR for:
    -- - c0..c3 (continuations)
    -- - c4,c5 (data regs: cells)
    -- - c7 (tuple)
    --
    -- We currently need:
    -- - c0,c1 for BOOLAND/BOOLOR/COMPOSBOTH
    -- - c2 for TRY (exception handler chaining)
    -- - c4,c5,c7 for real-tx fixtures.
    c0 : Option Continuation := none
    c1 : Option Continuation := none
    c2 : Option Continuation := none
    c3 : Option Continuation := none
    c4 : Option Cell := none
    c5 : Option Cell := none
    c7 : Option (Array Value) := none
    deriving Repr

  structure OrdCdata where
    stack : Array Value := #[]
    nargs : Int := -1
    deriving Repr

  inductive Continuation : Type
    | ordinary (code : Slice) (savedC0 : Continuation) (cregs : OrdCregs) (cdata : OrdCdata)
    | envelope (ext : Continuation) (cregs : OrdCregs) (cdata : OrdCdata)
    | quit (exitCode : Int)
    | excQuit
    | whileCond (cond : Continuation) (body : Continuation) (after : Continuation)
    | whileBody (cond : Continuation) (body : Continuation) (after : Continuation)
    | untilBody (body : Continuation) (after : Continuation)
    | repeatBody (body : Continuation) (after : Continuation) (count : Nat)
    | againBody (body : Continuation)
    deriving Repr

  inductive Value : Type
    | int (i : IntVal)
    | cell (c : Cell)
    | slice (s : Slice)
    | builder (b : Builder)
    | tuple (t : Array Value)
    | cont (k : Continuation)
    | null
    deriving Repr
end

def OrdCregs.empty : OrdCregs := {}

def OrdCregs.defineFromValue (cregs : OrdCregs) (idx : Nat) (v : Value) : Except Excno OrdCregs := do
  match idx, v with
  | 0, .cont k =>
      match cregs.c0 with
      | none => pure { cregs with c0 := some k }
      | some _ => throw .typeChk
  | 1, .cont k =>
      match cregs.c1 with
      | none => pure { cregs with c1 := some k }
      | some _ => throw .typeChk
  | 2, .cont k =>
      match cregs.c2 with
      | none => pure { cregs with c2 := some k }
      | some _ => throw .typeChk
  | 3, .cont k =>
      match cregs.c3 with
      | none => pure { cregs with c3 := some k }
      | some _ => throw .typeChk
  | 4, .cell c =>
      match cregs.c4 with
      | none => pure { cregs with c4 := some c }
      | some _ => throw .typeChk
  | 5, .cell c =>
      match cregs.c5 with
      | none => pure { cregs with c5 := some c }
      | some _ => throw .typeChk
  | 7, .tuple t =>
      -- `define_c7` in C++ never fails; it just keeps the existing one if present.
      match cregs.c7 with
      | none => pure { cregs with c7 := some t }
      | some _ => pure cregs
  | _, _ =>
      throw .typeChk

end TvmLean
