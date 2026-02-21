import Contracts.LoopCounter.Program

namespace Contracts.LoopCounter.Spec

open Contracts.LoopCounter.Program

abbrev SpecState := LoopState

def init (n : Nat) : SpecState :=
  initState n

def run (fuel : Nat) (st : SpecState) : SpecState :=
  runCounter fuel st

def runFromInit (n : Nat) : SpecState :=
  run n (init n)

def SumInvariant (n : Nat) (st : SpecState) : Prop :=
  st.counter + st.remaining = n

def Pre (_n : Nat) : Prop :=
  True

def Post (n : Nat) (st : SpecState) : Prop :=
  st.remaining = 0 ∧ st.counter = n

end Contracts.LoopCounter.Spec
