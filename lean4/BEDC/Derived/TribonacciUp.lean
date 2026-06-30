namespace BEDC.Derived.TribonacciUp

def tribonacci : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => tribonacci n + tribonacci (n + 1) + tribonacci (n + 2)

structure State3 where
  top : Nat
  middle : Nat
  bottom : Nat

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

def seed : State3 :=
  ⟨1, 1, 0⟩

def stepState : State3 -> State3
  | ⟨top, middle, bottom⟩ => ⟨top + middle + bottom, top, middle⟩

def state : Nat -> State3
  | 0 => seed
  | n + 1 => stepState (state n)

def matrix : Mat3 :=
  ⟨1, 1, 1,
    1, 0, 0,
    0, 1, 0⟩

def matVec (X : Mat3) (v : State3) : State3 :=
  ⟨X.aa * v.top + X.ab * v.middle + X.ac * v.bottom,
    X.ba * v.top + X.bb * v.middle + X.bc * v.bottom,
    X.ca * v.top + X.cb * v.middle + X.cc * v.bottom⟩

def matrixPowerState : Nat -> State3
  | 0 => seed
  | n + 1 => matVec matrix (matrixPowerState n)

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

private theorem add_three_reverse (a b c : Nat) :
    a + b + c = c + b + a := by
  calc
    a + b + c = c + (a + b) := by
      rw [Nat.add_comm (a + b) c]
    _ = c + (b + a) := by
      rw [Nat.add_comm a b]
    _ = c + b + a := by
      rw [Nat.add_assoc]

private theorem matrix_step_eq_step (v : State3) :
    matVec matrix v = stepState v := by
  cases v with
  | mk top middle bottom =>
      apply state3_eq
      · change 1 * top + 1 * middle + 1 * bottom =
          top + middle + bottom
        rw [Nat.one_mul, Nat.one_mul, Nat.one_mul]
      · change 1 * top + 0 * middle + 0 * bottom = top
        rw [Nat.one_mul, Nat.zero_mul, Nat.zero_mul]
        exact (Nat.add_zero (top + 0)).trans (Nat.add_zero top)
      · change 0 * top + 1 * middle + 0 * bottom = middle
        rw [Nat.zero_mul, Nat.one_mul, Nat.zero_mul]
        exact (congrArg (fun x => x + 0) (Nat.zero_add middle)).trans
          (Nat.add_zero middle)

private theorem state_eq_tribonacci_triple_pair (n : Nat) :
    state n =
      ⟨tribonacci (n + 2), tribonacci (n + 1), tribonacci n⟩ ∧
    state (n + 1) =
      ⟨tribonacci (n + 3), tribonacci (n + 2), tribonacci (n + 1)⟩ := by
  induction n with
  | zero =>
      constructor
      · rfl
      · rfl
  | succ n ih =>
      constructor
      · exact ih.right
      · rw [state, ih.right]
        apply state3_eq
        · change tribonacci (n + 3) + tribonacci (n + 2) +
            tribonacci (n + 1) =
              tribonacci (n + 1) + tribonacci (n + 2) +
                tribonacci (n + 3)
          exact add_three_reverse
            (tribonacci (n + 3)) (tribonacci (n + 2))
            (tribonacci (n + 1))
        · change tribonacci (n + 3) = tribonacci (n + 1 + 2)
          rfl
        · change tribonacci (n + 2) = tribonacci (n + 1 + 1)
          rfl

private theorem matrix_power_state_pair (n : Nat) :
    matrixPowerState n = state n ∧
    matrixPowerState (n + 1) = state (n + 1) := by
  induction n with
  | zero =>
      constructor
      · rfl
      · rw [matrixPowerState, matrix_step_eq_step]
        rfl
  | succ n ih =>
      constructor
      · exact ih.right
      · change matVec matrix (matrixPowerState (n + 1)) =
          stepState (state (n + 1))
        rw [ih.right, matrix_step_eq_step]

theorem tribonacci_zero :
    tribonacci 0 = 0 := by
  rfl

theorem tribonacci_one :
    tribonacci 1 = 1 := by
  rfl

theorem tribonacci_two :
    tribonacci 2 = 1 := by
  rfl

theorem tribonacci_recurrence (n : Nat) :
    tribonacci (n + 3) =
      tribonacci n + tribonacci (n + 1) + tribonacci (n + 2) := by
  rfl

theorem tribonacci_three :
    tribonacci 3 = 2 := by
  rfl

theorem tribonacci_four :
    tribonacci 4 = 4 := by
  rfl

theorem tribonacci_five :
    tribonacci 5 = 7 := by
  rfl

theorem tribonacci_six :
    tribonacci 6 = 13 := by
  rfl

theorem tribonacci_seven :
    tribonacci 7 = 24 := by
  rfl

theorem state_eq_tribonacci_triple (n : Nat) :
    state n =
      ⟨tribonacci (n + 2), tribonacci (n + 1), tribonacci n⟩ :=
  (state_eq_tribonacci_triple_pair n).left

theorem matrix_power_state (n : Nat) :
    matrixPowerState n = state n :=
  (matrix_power_state_pair n).left

theorem matrix_power_tribonacci (n : Nat) :
    matrixPowerState n =
      ⟨tribonacci (n + 2), tribonacci (n + 1), tribonacci n⟩ := by
  rw [matrix_power_state, state_eq_tribonacci_triple]

theorem matrix_power_top (n : Nat) :
    (matrixPowerState n).top = tribonacci (n + 2) := by
  rw [matrix_power_tribonacci]

theorem matrix_power_middle (n : Nat) :
    (matrixPowerState n).middle = tribonacci (n + 1) := by
  rw [matrix_power_tribonacci]

theorem matrix_power_bottom (n : Nat) :
    (matrixPowerState n).bottom = tribonacci n := by
  rw [matrix_power_tribonacci]

theorem tribonacci_sum_identity (n : Nat) :
    tribonacci n + tribonacci (n + 1) + tribonacci (n + 2) =
      tribonacci (n + 3) := by
  rfl

theorem tribonacci_shifted_reverse_sum (n : Nat) :
    tribonacci (n + 4) =
      tribonacci (n + 3) + tribonacci (n + 2) + tribonacci (n + 1) := by
  change tribonacci (n + 1) + tribonacci (n + 2) + tribonacci (n + 3) =
    tribonacci (n + 3) + tribonacci (n + 2) + tribonacci (n + 1)
  exact add_three_reverse
    (tribonacci (n + 1)) (tribonacci (n + 2)) (tribonacci (n + 3))

theorem tribonacci_prefix_induction
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

theorem tribonacci_strong_induction
    {P : Nat -> Prop}
    (hzero : P 0) (hone : P 1) (htwo : P 2)
    (hstep : ∀ n : Nat, P n -> P (n + 1) -> P (n + 2) -> P (n + 3)) :
    ∀ n : Nat, P n := by
  intro n
  exact (tribonacci_prefix_induction hzero hone htwo hstep n).left

theorem tribonacci_step_monotone (n : Nat) :
    tribonacci n ≤ tribonacci (n + 1) := by
  cases n with
  | zero =>
      exact Nat.zero_le 1
  | succ n =>
      cases n with
      | zero =>
          exact Nat.le_refl 1
      | succ n =>
          change tribonacci (n + 2) ≤
            tribonacci n + tribonacci (n + 1) + tribonacci (n + 2)
          exact
            Nat.le_add_left
              (tribonacci (n + 2))
              (tribonacci n + tribonacci (n + 1))

theorem tribonacci_monotone {m n : Nat} :
    m ≤ n -> tribonacci m ≤ tribonacci n := by
  intro h
  induction h with
  | refl =>
      exact Nat.le_refl _
  | step _ ih =>
      exact Nat.le_trans ih (tribonacci_step_monotone _)

theorem tribonacci_monotone_at (m n : Nat) :
    m ≤ n -> tribonacci m ≤ tribonacci n := by
  exact tribonacci_monotone

end BEDC.Derived.TribonacciUp
