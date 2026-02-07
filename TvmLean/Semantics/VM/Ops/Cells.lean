import TvmLean.Model
import TvmLean.Semantics.VM.Monad
import TvmLean.Semantics.VM.Ops.Stack

namespace TvmLean

def VM.popCell : VM Cell := do
  let v ← VM.pop
  match v with
  | .cell c => return c
  | _ => throw .typeChk

def VM.popSlice : VM Slice := do
  let v ← VM.pop
  match v with
  | .slice s => return s
  | _ => throw .typeChk

def VM.popBuilder : VM Builder := do
  let v ← VM.pop
  match v with
  | .builder b => return b
  | _ => throw .typeChk

def VM.popMaybeCell : VM (Option Cell) := do
  let v ← VM.pop
  match v with
  | .null => return none
  | .cell c => return some c
  | _ => throw .typeChk

end TvmLean
