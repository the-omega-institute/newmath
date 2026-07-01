namespace BEDC.Derived.MahonianNumberUp

def inversionInsertSum (row : Nat -> Nat) : Nat -> Nat -> Nat
  | target, 0 => row target
  | target, Nat.succ slots =>
      inversionInsertSum row target slots +
        if Nat.succ slots <= target then row (target - Nat.succ slots) else 0

def mahonianNumber : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ n, target => inversionInsertSum (mahonianNumber n) target n

theorem inversionInsertSum_zero_target (row : Nat -> Nat) (slots : Nat) :
    inversionInsertSum row 0 slots = row 0 := by
  induction slots with
  | zero =>
      rfl
  | succ slots ih =>
      change inversionInsertSum row 0 slots + 0 = row 0
      rw [ih, Nat.add_zero]

theorem inversionInsertSum_succ_slots
    (row : Nat -> Nat) (target slots : Nat) :
    inversionInsertSum row target (Nat.succ slots) =
      inversionInsertSum row target slots +
        if Nat.succ slots <= target then row (target - Nat.succ slots) else 0 := by
  rfl

theorem mahonian_zero_zero :
    mahonianNumber 0 0 = 1 := by
  rfl

theorem mahonian_zero_succ (target : Nat) :
    mahonianNumber 0 (Nat.succ target) = 0 := by
  rfl

theorem mahonian_succ (n target : Nat) :
    mahonianNumber (Nat.succ n) target =
      inversionInsertSum (mahonianNumber n) target n := by
  rfl

theorem mahonian_zero_inversion (n : Nat) :
    mahonianNumber n 0 = 1 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change inversionInsertSum (mahonianNumber n) 0 n = 1
      rw [inversionInsertSum_zero_target]
      exact ih

theorem mahonian_row_two :
    mahonianNumber 2 0 = 1 ∧
      mahonianNumber 2 1 = 1 ∧
        mahonianNumber 2 2 = 0 := by
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

theorem mahonian_row_three :
    mahonianNumber 3 0 = 1 ∧
      mahonianNumber 3 1 = 2 ∧
        mahonianNumber 3 2 = 2 ∧
          mahonianNumber 3 3 = 1 ∧
            mahonianNumber 3 4 = 0 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · rfl

theorem MahonianNumberUp_constructive_export :
    mahonianNumber 0 0 = 1 ∧
      (∀ target : Nat, mahonianNumber 0 (Nat.succ target) = 0) ∧
      (∀ n target : Nat,
        mahonianNumber (Nat.succ n) target =
          inversionInsertSum (mahonianNumber n) target n) ∧
      (∀ n : Nat, mahonianNumber n 0 = 1) ∧
      mahonianNumber 3 0 = 1 ∧
      mahonianNumber 3 1 = 2 ∧
      mahonianNumber 3 2 = 2 ∧
      mahonianNumber 3 3 = 1 := by
  constructor
  · exact mahonian_zero_zero
  · constructor
    · intro target
      exact mahonian_zero_succ target
    · constructor
      · intro n target
        exact mahonian_succ n target
      · constructor
        · intro n
          exact mahonian_zero_inversion n
        · constructor
          · exact mahonian_row_three.left
          · constructor
            · exact mahonian_row_three.right.left
            · constructor
              · exact mahonian_row_three.right.right.left
              · exact mahonian_row_three.right.right.right.left

end BEDC.Derived.MahonianNumberUp
