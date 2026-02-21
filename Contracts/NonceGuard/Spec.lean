import Contracts.NonceGuard.Program

namespace Contracts.NonceGuard.Spec

open TvmLean
open Contracts.NonceGuard.Program

structure SpecState where
  nonceRoot : Option Cell
  deriving Repr

def init : SpecState :=
  { nonceRoot := none }

def mark (st : SpecState) (nonce : Nat) : Except Excno (Bool × SpecState) := do
  let (root', ok, _, _) ← addNonce st.nonceRoot nonce
  return (ok, { st with nonceRoot := root' })

def isUsed (st : SpecState) (nonce : Nat) : Except Excno Bool := do
  let found ← lookupNonce st.nonceRoot nonce
  return found.isSome

def firstAccepts? (nonce : Nat) : Except Excno Bool := do
  let (ok, _) ← mark init nonce
  return ok

def replayPair? (nonce : Nat) : Except Excno (Bool × Bool) := do
  let (ok1, st1) ← mark init nonce
  let (ok2, _) ← mark st1 nonce
  return (ok1, ok2)

def usedAfterFirstMark? (nonce : Nat) : Except Excno Bool := do
  let (_, st1) ← mark init nonce
  isUsed st1 nonce

def resultAccepted (res : Except Excno Bool) : Bool :=
  match res with
  | .ok true => true
  | _ => false

def resultReplayRejected (res : Except Excno (Bool × Bool)) : Bool :=
  match res with
  | .ok (true, false) => true
  | _ => false

def Pre (_nonce : Nat) : Prop :=
  True

def PostFirstAccept (nonce : Nat) : Prop :=
  resultAccepted (firstAccepts? nonce) = true

def PostReplayReject (nonce : Nat) : Prop :=
  resultReplayRejected (replayPair? nonce) = true

def PostMarkedAfterFirstUse (nonce : Nat) : Prop :=
  resultAccepted (usedAfterFirstMark? nonce) = true

end Contracts.NonceGuard.Spec
