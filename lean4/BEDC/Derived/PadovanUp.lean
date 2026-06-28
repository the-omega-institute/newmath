import BEDC.Algebra.Rel.Basic

namespace BEDC.Derived.PadovanUp

def padovan : Nat -> Nat
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => padovan (n + 1) + padovan n

def perrin : Nat -> Nat
  | 0 => 3
  | 1 => 0
  | 2 => 2
  | n + 3 => perrin (n + 1) + perrin n

structure State3 where
  top : Nat
  middle : Nat
  bottom : Nat
deriving DecidableEq

structure Mat3 where
  aa : Nat
  ab : Nat
  ac : Nat
  ba : Nat
  bb : Nat
  bc : Nat
  ca : Nat
  cb : Nat
  cc : Nat
deriving DecidableEq

def companionMatrix : Mat3 :=
  ⟨0, 1, 1,
    1, 0, 0,
    0, 1, 0⟩

def matVec (X : Mat3) (v : State3) : State3 :=
  ⟨X.aa * v.top + X.ab * v.middle + X.ac * v.bottom,
    X.ba * v.top + X.bb * v.middle + X.bc * v.bottom,
    X.ca * v.top + X.cb * v.middle + X.cc * v.bottom⟩

def stepState : State3 -> State3
  | ⟨top, middle, bottom⟩ => ⟨middle + bottom, top, middle⟩

def padovanSeed : State3 :=
  ⟨1, 1, 1⟩

def perrinSeed : State3 :=
  ⟨2, 0, 3⟩

def padovanState : Nat -> State3
  | 0 => padovanSeed
  | n + 1 => stepState (padovanState n)

def perrinState : Nat -> State3
  | 0 => perrinSeed
  | n + 1 => stepState (perrinState n)

def matrixPowerStateFrom (seed : State3) : Nat -> State3
  | 0 => seed
  | n + 1 => matVec companionMatrix (matrixPowerStateFrom seed n)

abbrev padovanMatrixState : Nat -> State3 :=
  matrixPowerStateFrom padovanSeed

abbrev perrinMatrixState : Nat -> State3 :=
  matrixPowerStateFrom perrinSeed

private theorem state3_eq {x y : State3}
    (htop : x.top = y.top) (hmiddle : x.middle = y.middle)
    (hbottom : x.bottom = y.bottom) :
    x = y := by
  cases x with
  | mk top middle bottom =>
      cases y with
      | mk top' middle' bottom' =>
          cases htop
          cases hmiddle
          cases hbottom
          rfl

private theorem matrix_step_eq_step (v : State3) :
    matVec companionMatrix v = stepState v := by
  cases v with
  | mk top middle bottom =>
      apply state3_eq
      · change 0 * top + 1 * middle + 1 * bottom = middle + bottom
        rw [Nat.zero_mul, Nat.one_mul, Nat.one_mul, Nat.zero_add]
      · change 1 * top + 0 * middle + 0 * bottom = top
        rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul]
        exact (Nat.add_zero (top + 0)).trans (Nat.add_zero top)
      · change 0 * top + 1 * middle + 0 * bottom = middle
        rw [Nat.zero_mul, Nat.one_mul, Nat.zero_mul]
        exact (congrArg (fun x => x + 0) (Nat.zero_add middle)).trans
          (Nat.add_zero middle)

private theorem padovan_state_pair (n : Nat) :
    padovanState n =
      ⟨padovan (n + 2), padovan (n + 1), padovan n⟩ ∧
    padovanState (n + 1) =
      ⟨padovan (n + 3), padovan (n + 2), padovan (n + 1)⟩ := by
  induction n with
  | zero =>
      constructor
      · rfl
      · rfl
  | succ n ih =>
      constructor
      · exact ih.right
      · rw [padovanState, ih.right]
        apply state3_eq
        · change padovan (n + 2) + padovan (n + 1) = padovan (n + 4)
          rfl
        · change padovan (n + 3) = padovan (n + 1 + 2)
          rfl
        · change padovan (n + 2) = padovan (n + 1 + 1)
          rfl

private theorem perrin_state_pair (n : Nat) :
    perrinState n =
      ⟨perrin (n + 2), perrin (n + 1), perrin n⟩ ∧
    perrinState (n + 1) =
      ⟨perrin (n + 3), perrin (n + 2), perrin (n + 1)⟩ := by
  induction n with
  | zero =>
      constructor
      · rfl
      · rfl
  | succ n ih =>
      constructor
      · exact ih.right
      · rw [perrinState, ih.right]
        apply state3_eq
        · change perrin (n + 2) + perrin (n + 1) = perrin (n + 4)
          rfl
        · change perrin (n + 3) = perrin (n + 1 + 2)
          rfl
        · change perrin (n + 2) = perrin (n + 1 + 1)
          rfl

private theorem matrix_state_pair (seed : State3) (state : Nat -> State3)
    (hzero : state 0 = seed)
    (hstep : ∀ n : Nat, state (n + 1) = stepState (state n))
    (n : Nat) :
    matrixPowerStateFrom seed n = state n ∧
    matrixPowerStateFrom seed (n + 1) = state (n + 1) := by
  induction n with
  | zero =>
      constructor
      · exact hzero.symm
      · calc
          matrixPowerStateFrom seed (0 + 1) = stepState seed := by
            change matVec companionMatrix (matrixPowerStateFrom seed 0) = stepState seed
            rw [matrix_step_eq_step]
            rfl
          _ = stepState seed := by
            rfl
          _ = stepState (state 0) := by
            rw [hzero]
          _ = state (0 + 1) := (hstep 0).symm
  | succ n ih =>
      constructor
      · exact ih.right
      · rw [matrixPowerStateFrom, matrix_step_eq_step, ih.right]
        exact (hstep (n + 1)).symm

theorem padovan_zero :
    padovan 0 = 1 := by
  rfl

theorem padovan_one :
    padovan 1 = 1 := by
  rfl

theorem padovan_two :
    padovan 2 = 1 := by
  rfl

theorem padovan_recurrence (n : Nat) :
    padovan (n + 3) = padovan (n + 1) + padovan n := by
  rfl

theorem padovan_three :
    padovan 3 = 2 := by
  rfl

theorem padovan_four :
    padovan 4 = 2 := by
  rfl

theorem padovan_five :
    padovan 5 = 3 := by
  rfl

theorem padovan_six :
    padovan 6 = 4 := by
  rfl

theorem padovan_seven :
    padovan 7 = 5 := by
  rfl

theorem padovan_eight :
    padovan 8 = 7 := by
  rfl

theorem padovan_state_eq (n : Nat) :
    padovanState n =
      ⟨padovan (n + 2), padovan (n + 1), padovan n⟩ :=
  (padovan_state_pair n).left

theorem padovan_matrix_state (n : Nat) :
    padovanMatrixState n = padovanState n :=
  (matrix_state_pair padovanSeed padovanState rfl (fun _ => rfl) n).left

theorem padovan_matrix_power (n : Nat) :
    padovanMatrixState n =
      ⟨padovan (n + 2), padovan (n + 1), padovan n⟩ := by
  rw [padovan_matrix_state, padovan_state_eq]

theorem padovan_matrix_top (n : Nat) :
    (padovanMatrixState n).top = padovan (n + 2) := by
  rw [padovan_matrix_power]

theorem padovan_matrix_middle (n : Nat) :
    (padovanMatrixState n).middle = padovan (n + 1) := by
  rw [padovan_matrix_power]

theorem padovan_matrix_bottom (n : Nat) :
    (padovanMatrixState n).bottom = padovan n := by
  rw [padovan_matrix_power]

theorem padovan_four_step (n : Nat) :
    padovan (n + 4) = padovan (n + 2) + padovan (n + 1) := by
  rfl

theorem padovan_five_step_sum (n : Nat) :
    padovan (n + 5) =
      padovan n + padovan (n + 1) + padovan (n + 2) := by
  calc
    padovan (n + 5) = padovan (n + 3) + padovan (n + 2) := by
      rfl
    _ = (padovan (n + 1) + padovan n) + padovan (n + 2) := by
      rfl
    _ = (padovan n + padovan (n + 1)) + padovan (n + 2) := by
      rw [Nat.add_comm (padovan (n + 1)) (padovan n)]
    _ = padovan n + padovan (n + 1) + padovan (n + 2) := by
      rfl

theorem padovan_prefix_induction
    {P : Nat -> Prop}
    (hzero : P 0) (hone : P 1) (htwo : P 2)
    (hstep : ∀ n : Nat, P n -> P (n + 1) -> P (n + 2) -> P (n + 3)) :
    ∀ n : Nat, P n ∧ P (n + 1) ∧ P (n + 2) := by
  intro n
  induction n with
  | zero =>
      exact ⟨hzero, hone, htwo⟩
  | succ n ih =>
      exact ⟨ih.right.left, ih.right.right,
        hstep n ih.left ih.right.left ih.right.right⟩

theorem padovan_strong_induction
    {P : Nat -> Prop}
    (hzero : P 0) (hone : P 1) (htwo : P 2)
    (hstep : ∀ n : Nat, P n -> P (n + 1) -> P (n + 2) -> P (n + 3)) :
    ∀ n : Nat, P n := by
  intro n
  exact (padovan_prefix_induction hzero hone htwo hstep n).left

theorem perrin_zero :
    perrin 0 = 3 := by
  rfl

theorem perrin_one :
    perrin 1 = 0 := by
  rfl

theorem perrin_two :
    perrin 2 = 2 := by
  rfl

theorem perrin_recurrence (n : Nat) :
    perrin (n + 3) = perrin (n + 1) + perrin n := by
  rfl

theorem perrin_three :
    perrin 3 = 3 := by
  rfl

theorem perrin_four :
    perrin 4 = 2 := by
  rfl

theorem perrin_five :
    perrin 5 = 5 := by
  rfl

theorem perrin_state_eq (n : Nat) :
    perrinState n =
      ⟨perrin (n + 2), perrin (n + 1), perrin n⟩ :=
  (perrin_state_pair n).left

theorem perrin_matrix_state (n : Nat) :
    perrinMatrixState n = perrinState n :=
  (matrix_state_pair perrinSeed perrinState rfl (fun _ => rfl) n).left

theorem perrin_matrix_power (n : Nat) :
    perrinMatrixState n =
      ⟨perrin (n + 2), perrin (n + 1), perrin n⟩ := by
  rw [perrin_matrix_state, perrin_state_eq]

theorem perrin_padovan_common_companion (n : Nat) :
    perrinMatrixState (n + 1) = matVec companionMatrix (perrinMatrixState n) ∧
      padovanMatrixState (n + 1) = matVec companionMatrix (padovanMatrixState n) := by
  constructor
  · rfl
  · rfl

theorem perrin_padovan_initial_contact :
    perrin 5 = padovan 7 := by
  rfl

def plasticCubicRel {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x : A) : Prop :=
  r (R.mul (R.mul x x) x) (R.add x R.one)

structure PlasticNumberRelation {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) where
  root : A
  cubic : plasticCubicRel R root

theorem plasticCubicRel_readback {A : Type u} {r : A -> A -> Prop}
    (R : BEDC.Algebra.Rel.RelCommRing A r) (x : A) :
    plasticCubicRel R x =
      r (R.mul (R.mul x x) x) (R.add x R.one) := by
  rfl

end BEDC.Derived.PadovanUp
