import Contracts.ToyCounter.Program

namespace Contracts.ToyCounter.Spec

open TvmLean
open Contracts.ToyCounter.Program

structure SpecState where
  c4 : Cell
  deriving Repr

def init (x : Counter32) : SpecState :=
  { c4 := initialC4 x }

def run (st : SpecState) : Except Excno SpecState := do
  let x ← decodeCounter st.c4
  let x' := (x + 1) % (2 ^ 32)
  return { st with c4 := encodeCounter x' }

def runFromInit (x : Counter32) : Except Excno SpecState :=
  run (init x)

def Pre (_x : Counter32) : Prop := True

def Post (x : Counter32) (st1 : SpecState) : Prop :=
  st1.c4 = encodeCounter ((encodedInputValue x + 1) % (2 ^ 32))

end Contracts.ToyCounter.Spec
