namespace BEDC.Derived.TribonacciUp

def tribonacci : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => tribonacci n + tribonacci (n + 1) + tribonacci (n + 2)

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
