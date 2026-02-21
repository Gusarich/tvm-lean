import Contracts.DictCounter.Program

namespace Contracts.DictCounter.Spec

open TvmLean
open Contracts.DictCounter.Program

structure SpecState where
  dictRoot : Option Cell
  deriving Repr

def init : SpecState :=
  { dictRoot := none }

def lookupCounter (st : SpecState) (n : Nat) : Except Excno (Option Slice) :=
  lookup st.dictRoot (keyFromNat n)

def deleteCounter (st : SpecState) (n : Nat) :
    Except Excno (Option Slice × SpecState × Nat × Array Cell) := do
  let (oldVal, root', created, loaded) ← deleteWithTrace st.dictRoot (keyFromNat n)
  return (oldVal, { st with dictRoot := root' }, created, loaded)

def Pre (_n : Nat) : Prop := True

def PostLookup (res : Except Excno (Option Slice)) : Prop :=
  res = .ok none

def PostDelete (res : Except Excno (Option Slice × SpecState × Nat × Array Cell)) : Prop :=
  res = .ok (none, init, 0, #[])

end Contracts.DictCounter.Spec
