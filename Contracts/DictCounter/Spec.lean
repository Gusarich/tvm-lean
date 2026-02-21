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

def setCounter (st : SpecState) (n : Nat) :
    Except Excno (Bool × SpecState × Nat × Array Cell) := do
  let (root', ok, created, loaded) ← setDefaultWithTrace st.dictRoot (keyFromNat n)
  return (ok, { st with dictRoot := root' }, created, loaded)

def deleteCounter (st : SpecState) (n : Nat) :
    Except Excno (Option Slice × SpecState × Nat × Array Cell) := do
  let (oldVal, root', created, loaded) ← deleteWithTrace st.dictRoot (keyFromNat n)
  return (oldVal, { st with dictRoot := root' }, created, loaded)

def setThenLookupCounter (st : SpecState) (setN lookupN : Nat) :
    Except Excno (Bool × Option Slice × SpecState × Nat × Array Cell) := do
  let (ok, st', created, loaded) ← setCounter st setN
  let lookupRes ← lookupCounter st' lookupN
  return (ok, lookupRes, st', created, loaded)

def seededState (n : Nat) : SpecState :=
  match setCounter init n with
  | .ok (_, st', _, _) => st'
  | .error _ => init

def seeded : SpecState :=
  seededState 0

def seededSetThenLookup (setN lookupN : Nat) :
    Except Excno (Bool × Option Slice × SpecState × Nat × Array Cell) :=
  setThenLookupCounter seeded setN lookupN

def lookupHit (res : Except Excno (Option Slice)) : Bool :=
  match res with
  | .ok (some _) => true
  | _ => false

def deleteHit (res : Except Excno (Option Slice × SpecState × Nat × Array Cell)) : Bool :=
  match res with
  | .ok (some _, _, _, _) => true
  | _ => false

def deleteClearsRoot (res : Except Excno (Option Slice × SpecState × Nat × Array Cell)) : Bool :=
  match res with
  | .ok (some _, st', _, _) => !st'.dictRoot.isSome
  | _ => false

def setThenLookupHit (res : Except Excno (Bool × Option Slice × SpecState × Nat × Array Cell)) : Bool :=
  match res with
  | .ok (true, some _, _, _, _) => true
  | _ => false

def setThenLookupMiss (res : Except Excno (Bool × Option Slice × SpecState × Nat × Array Cell)) : Bool :=
  match res with
  | .ok (true, none, _, _, _) => true
  | _ => false

def Pre (_n : Nat) : Prop := True

def PostLookup (res : Except Excno (Option Slice)) : Prop :=
  res = .ok none

def PostDelete (res : Except Excno (Option Slice × SpecState × Nat × Array Cell)) : Prop :=
  res = .ok (none, init, 0, #[])

def PostSeeded (st : SpecState) : Prop :=
  st.dictRoot.isSome = true

def PostLookupHit (res : Except Excno (Option Slice)) : Prop :=
  lookupHit res = true

def PostDeleteHit (res : Except Excno (Option Slice × SpecState × Nat × Array Cell)) : Prop :=
  deleteHit res = true

def PostDeleteClearsRoot (res : Except Excno (Option Slice × SpecState × Nat × Array Cell)) : Prop :=
  deleteClearsRoot res = true

def PostSetThenLookupHit
    (res : Except Excno (Bool × Option Slice × SpecState × Nat × Array Cell)) : Prop :=
  setThenLookupHit res = true

def PostSetThenLookupMiss
    (res : Except Excno (Bool × Option Slice × SpecState × Nat × Array Cell)) : Prop :=
  setThenLookupMiss res = true

end Contracts.DictCounter.Spec
