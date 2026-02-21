import TvmLean.Model

namespace Contracts.LoopCounter.Program

structure LoopState where
  remaining : Nat
  counter : Nat
  deriving Repr, DecidableEq

def loopDone (st : LoopState) : Bool :=
  st.remaining = 0

def loopStep (st : LoopState) : LoopState :=
  match st.remaining with
  | 0 => st
  | r + 1 => { remaining := r, counter := st.counter + 1 }

def runLoop {σ : Type} (fuel : Nat) (done : σ → Bool) (step : σ → σ) (st : σ) : σ :=
  match fuel with
  | 0 => st
  | fuel + 1 =>
      if done st then
        st
      else
        runLoop fuel done step (step st)

theorem runLoop_preserves {σ : Type}
    (done : σ → Bool) (step : σ → σ) (Inv : σ → Prop)
    (hstep : ∀ s, done s = false → Inv s → Inv (step s)) :
    ∀ fuel s, Inv s → Inv (runLoop fuel done step s) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s hInv
      simpa [runLoop] using hInv
  | succ fuel ih =>
      intro s hInv
      cases hdone : done s with
      | false =>
          simp [runLoop, hdone]
          exact ih (step s) (hstep s hdone hInv)
      | true =>
          simpa [runLoop, hdone] using hInv

theorem loopStep_preserves_sum (st : LoopState) :
    (loopStep st).counter + (loopStep st).remaining = st.counter + st.remaining := by
  cases hrem : st.remaining with
  | zero =>
      simp [loopStep, hrem]
  | succ r =>
      simp [loopStep, hrem, Nat.add_left_comm, Nat.add_comm]

def runCounter (fuel : Nat) (st : LoopState) : LoopState :=
  runLoop fuel loopDone loopStep st

def initState (n : Nat) : LoopState :=
  { remaining := n, counter := 0 }

def runFromInit (n : Nat) : LoopState :=
  runCounter n (initState n)

theorem runCounter_preserves_sum (fuel : Nat) (st : LoopState) :
    (runCounter fuel st).counter + (runCounter fuel st).remaining = st.counter + st.remaining := by
  let Inv : LoopState → Prop := fun s =>
    s.counter + s.remaining = st.counter + st.remaining
  have hstep :
      ∀ s, loopDone s = false → Inv s → Inv (loopStep s) := by
    intro s _ hInv
    unfold Inv at *
    calc
      (loopStep s).counter + (loopStep s).remaining
          = s.counter + s.remaining := loopStep_preserves_sum s
      _ = st.counter + st.remaining := hInv
  have hInv0 : Inv st := by
    simp [Inv]
  have hInvFinal : Inv (runCounter fuel st) := by
    simpa [runCounter] using
      runLoop_preserves (done := loopDone) (step := loopStep) (Inv := Inv) hstep fuel st hInv0
  simpa [Inv] using hInvFinal

theorem runCounter_remaining_zero (fuel counter : Nat) :
    (runCounter fuel { remaining := fuel, counter := counter }).remaining = 0 := by
  induction fuel generalizing counter with
  | zero =>
      simp [runCounter, runLoop]
  | succ fuel ih =>
      simpa [runCounter, runLoop, loopDone, loopStep] using
        ih (counter := counter + 1)

theorem runFromInit_remaining_zero (n : Nat) :
    (runFromInit n).remaining = 0 := by
  simpa [runFromInit, initState] using
    runCounter_remaining_zero (fuel := n) (counter := 0)

end Contracts.LoopCounter.Program
