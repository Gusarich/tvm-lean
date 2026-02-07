import TvmLean.Model.Instr.Asm.Cp0

namespace TvmLean

structure Regs where
  c0 : Continuation
  c1 : Continuation
  c2 : Continuation
  c3 : Continuation
  c4 : Cell
  c5 : Cell
  c7 : Array Value
  deriving Repr

def Regs.initial : Regs :=
  { c0 := .quit 0
    c1 := .quit 1
    c2 := .excQuit
    c3 := .quit 11
    c4 := Cell.empty
    c5 := Cell.empty
    c7 := #[] }

end TvmLean
