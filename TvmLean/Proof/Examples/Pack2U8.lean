import TvmLean.Proof

namespace TvmLean.Proof.Examples.Pack2U8

open TvmLean

set_option maxHeartbeats 50000000
set_option maxRecDepth 65536

def program : List Instr :=
  [ .newc
  , .stu 8
  , .stu 8
  , .endc
  , .ctos
  , .ldu 16
  , .pop 0
  ]

def initState (x y : Int) : VmState :=
  let st := VmState.initial Cell.empty GasLimits.infty
  { st with stack := #[.int (.num y), .int (.num x)] }

def packed16 (x y : Int) : Int :=
  Int.ofNat (bitsToNat (natToBits x.toNat 8 ++ natToBits y.toNat 8))

def runSpecList : List Instr → VmState → Except Excno VmState
  | [], st => .ok st
  | instr :: rest, st =>
      let (res, st') := (execInstrSpecCore instr).run st
      match res with
      | .ok _ => runSpecList rest st'
      | .error e => .error e

def runProgramStack (x y : Int) : Except Excno Stack :=
  (runSpecList program (initState x y)).map VmState.stack

private def stackIsSingleInt (stack : Stack) (expected : Int) : Bool :=
  match stack.toList with
  | [.int (.num n)] => decide (n = expected)
  | _ => false

private def runMatchesPackedNat (x y : Nat) : Bool :=
  match runProgramStack (Int.ofNat x) (Int.ofNat y) with
  | .ok stack => stackIsSingleInt stack (packed16 (Int.ofNat x) (Int.ofNat y))
  | .error _ => false

private def runMatchesPackedFin (x y : Fin 256) : Bool :=
  runMatchesPackedNat x.1 y.1

private theorem runMatchesPackedFin_true : ∀ x y : Fin 256, runMatchesPackedFin x y = true := by
  native_decide

private theorem stackIsSingleInt_eq (stack : Stack) (expected : Int)
    (h : stackIsSingleInt stack expected = true) :
    stack = #[.int (.num expected)] := by
  unfold stackIsSingleInt at h
  cases hList : stack.toList with
  | nil =>
      simp [hList] at h
  | cons v rest =>
      cases rest with
      | nil =>
          cases v with
          | int iv =>
              cases iv with
              | nan =>
                  simp [hList] at h
              | num n =>
                  have hn : n = expected := by
                    simp [hList] at h
                    exact h
                  have hStackN : stack = #[.int (.num n)] := by
                    calc
                      stack = stack.toList.toArray := by
                        simp
                      _ = ([.int (.num n)] : List Value).toArray := by
                        simp [hList]
                      _ = #[.int (.num n)] := rfl
                  simpa [hn] using hStackN
          | cell _ =>
              simp [hList] at h
          | slice _ =>
              simp [hList] at h
          | builder _ =>
              simp [hList] at h
          | tuple _ =>
              simp [hList] at h
          | cont _ =>
              simp [hList] at h
          | null =>
              simp [hList] at h
      | cons _ _ =>
          simp [hList] at h

private theorem runMatchesPackedNat_implies_eq (x y : Nat)
    (h : runMatchesPackedNat x y = true) :
    runProgramStack (Int.ofNat x) (Int.ofNat y) =
      .ok #[.int (.num (packed16 (Int.ofNat x) (Int.ofNat y)))] := by
  unfold runMatchesPackedNat at h
  cases hRes : runProgramStack (Int.ofNat x) (Int.ofNat y) with
  | error e =>
      have hRes' : runProgramStack (↑x) (↑y) = .error e := by
        simpa using hRes
      simp [hRes'] at h
  | ok stack =>
      have hRes' : runProgramStack (↑x) (↑y) = .ok stack := by
        simpa using hRes
      have hStackOk : stackIsSingleInt stack (packed16 (Int.ofNat x) (Int.ofNat y)) = true := by
        simp [hRes'] at h
        exact h
      have hStack : stack = #[.int (.num (packed16 (Int.ofNat x) (Int.ofNat y)))] :=
        stackIsSingleInt_eq stack (packed16 (Int.ofNat x) (Int.ofNat y)) hStackOk
      simp [hStack]

theorem run_ok_stack_bits_fin (x y : Fin 256) :
    runProgramStack (Int.ofNat x.1) (Int.ofNat y.1) =
      .ok #[.int (.num (packed16 (Int.ofNat x.1) (Int.ofNat y.1)))] := by
  have hFin : runMatchesPackedFin x y = true := runMatchesPackedFin_true x y
  exact runMatchesPackedNat_implies_eq x.1 y.1 hFin

theorem run_ok_stack_bits_of_bounds (x y : Int)
    (hx0 : 0 ≤ x) (hx1 : x < 256) (hy0 : 0 ≤ y) (hy1 : y < 256) :
    runProgramStack x y =
      .ok #[.int (.num (packed16 x y))] := by
  have hxNatLt : x.toNat < 256 := (Int.toNat_lt hx0).2 (by simpa using hx1)
  have hyNatLt : y.toNat < 256 := (Int.toNat_lt hy0).2 (by simpa using hy1)
  let x8 : Fin 256 := ⟨x.toNat, hxNatLt⟩
  let y8 : Fin 256 := ⟨y.toNat, hyNatLt⟩
  have hNatEq :
      runProgramStack (Int.ofNat x.toNat) (Int.ofNat y.toNat) =
        .ok #[.int (.num (packed16 (Int.ofNat x.toNat) (Int.ofNat y.toNat)))] :=
    run_ok_stack_bits_fin x8 y8
  have hNatEqMax :
      runProgramStack (max x 0) (max y 0) =
        .ok #[.int (.num (packed16 (max x 0) (max y 0)))] := by
    simpa [packed16] using hNatEq
  have hxMax : max x 0 = x := Int.max_eq_left hx0
  have hyMax : max y 0 = y := Int.max_eq_left hy0
  simpa [hxMax, hyMax] using hNatEqMax

end TvmLean.Proof.Examples.Pack2U8
