namespace BEDC.Derived.EntringerNumberUp

def entringerRowFrom (previous : Nat -> Nat) (n : Nat) : Nat -> Nat
  | 0 => 0
  | Nat.succ k => entringerRowFrom previous n k + previous (n - k)

def entringerNumber : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ n, k => entringerRowFrom (entringerNumber n) n k

def zigzagByEntringer (n : Nat) : Nat :=
  entringerNumber n n

theorem entringer_zero_zero :
    entringerNumber 0 0 = 1 := by
  rfl

theorem entringer_zero_succ (k : Nat) :
    entringerNumber 0 (Nat.succ k) = 0 := by
  rfl

theorem entringer_succ_zero (n : Nat) :
    entringerNumber (Nat.succ n) 0 = 0 := by
  rfl

theorem entringer_succ_succ (n k : Nat) :
    entringerNumber (Nat.succ n) (Nat.succ k) =
      entringerNumber (Nat.succ n) k + entringerNumber n (n - k) := by
  rfl

theorem entringer_first_positive_column (n : Nat) :
    entringerNumber (Nat.succ n) 1 = entringerNumber n n := by
  change 0 + entringerNumber n (n - 0) = entringerNumber n n
  rw [Nat.sub_zero, Nat.zero_add]

theorem entringer_last_succ (n : Nat) :
    entringerNumber (Nat.succ n) (Nat.succ n) =
      entringerNumber (Nat.succ n) n + entringerNumber n 0 := by
  change entringerNumber (Nat.succ n) n + entringerNumber n (n - n) =
    entringerNumber (Nat.succ n) n + entringerNumber n 0
  rw [Nat.sub_self]

theorem zigzagByEntringer_zero :
    zigzagByEntringer 0 = 1 := by
  rfl

theorem zigzagByEntringer_one :
    zigzagByEntringer 1 = 1 := by
  rfl

theorem zigzagByEntringer_two :
    zigzagByEntringer 2 = 1 := by
  rfl

theorem zigzagByEntringer_three :
    zigzagByEntringer 3 = 2 := by
  rfl

theorem zigzagByEntringer_four :
    zigzagByEntringer 4 = 5 := by
  rfl

theorem entringer_row_three :
    entringerNumber 3 0 = 0 ∧
      entringerNumber 3 1 = 1 ∧
        entringerNumber 3 2 = 2 ∧
          entringerNumber 3 3 = 2 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

theorem EntringerNumberUp_constructive_export :
    zigzagByEntringer 0 = 1 ∧
      zigzagByEntringer 1 = 1 ∧
      zigzagByEntringer 2 = 1 ∧
      zigzagByEntringer 3 = 2 ∧
      zigzagByEntringer 4 = 5 ∧
      (∀ n : Nat,
        entringerNumber (Nat.succ n) 1 = entringerNumber n n) ∧
      (∀ n : Nat,
        entringerNumber (Nat.succ n) (Nat.succ n) =
          entringerNumber (Nat.succ n) n + entringerNumber n 0) := by
  constructor
  · exact zigzagByEntringer_zero
  · constructor
    · exact zigzagByEntringer_one
    · constructor
      · exact zigzagByEntringer_two
      · constructor
        · exact zigzagByEntringer_three
        · constructor
          · exact zigzagByEntringer_four
          · constructor
            · intro n
              exact entringer_first_positive_column n
            · intro n
              exact entringer_last_succ n

end BEDC.Derived.EntringerNumberUp
