namespace BEDC.Derived.CentralTrinomialUp

def trinomialCoeff : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ n, 0 => trinomialCoeff n 0
  | Nat.succ n, Nat.succ 0 => trinomialCoeff n 1 + trinomialCoeff n 0
  | Nat.succ n, Nat.succ (Nat.succ k) =>
      trinomialCoeff n (Nat.succ (Nat.succ k)) +
        trinomialCoeff n (Nat.succ k) + trinomialCoeff n k

def centralTrinomialNumber (n : Nat) : Nat :=
  trinomialCoeff n n

theorem trinomialCoeff_zero_zero :
    trinomialCoeff 0 0 = 1 := by
  rfl

theorem trinomialCoeff_zero_succ (k : Nat) :
    trinomialCoeff 0 (Nat.succ k) = 0 := by
  rfl

theorem trinomialCoeff_succ_zero (n : Nat) :
    trinomialCoeff (Nat.succ n) 0 = trinomialCoeff n 0 := by
  rfl

theorem trinomialCoeff_succ_one (n : Nat) :
    trinomialCoeff (Nat.succ n) 1 =
      trinomialCoeff n 1 + trinomialCoeff n 0 := by
  rfl

theorem trinomialCoeff_succ_succ_succ (n k : Nat) :
    trinomialCoeff (Nat.succ n) (Nat.succ (Nat.succ k)) =
      trinomialCoeff n (Nat.succ (Nat.succ k)) +
        trinomialCoeff n (Nat.succ k) + trinomialCoeff n k := by
  rfl

theorem centralTrinomial_zero :
    centralTrinomialNumber 0 = 1 := by
  rfl

theorem centralTrinomial_one :
    centralTrinomialNumber 1 = 1 := by
  rfl

theorem centralTrinomial_two :
    centralTrinomialNumber 2 = 3 := by
  rfl

theorem centralTrinomial_three :
    centralTrinomialNumber 3 = 7 := by
  rfl

theorem centralTrinomial_one_diagonal :
    centralTrinomialNumber 1 = trinomialCoeff 0 1 + trinomialCoeff 0 0 := by
  rfl

theorem centralTrinomial_succ_succ_diagonal (n : Nat) :
    centralTrinomialNumber (Nat.succ (Nat.succ n)) =
      trinomialCoeff (Nat.succ n) (Nat.succ (Nat.succ n)) +
        trinomialCoeff (Nat.succ n) (Nat.succ n) +
          trinomialCoeff (Nat.succ n) n := by
  rfl

theorem trinomialCoeff_row_one :
    trinomialCoeff 1 0 = 1 ∧
      trinomialCoeff 1 1 = 1 ∧
        trinomialCoeff 1 2 = 1 ∧
          trinomialCoeff 1 3 = 0 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

theorem CentralTrinomialUp_constructive_export :
    centralTrinomialNumber 0 = 1 ∧
      centralTrinomialNumber 1 = 1 ∧
      centralTrinomialNumber 2 = 3 ∧
      centralTrinomialNumber 3 = 7 ∧
      centralTrinomialNumber 1 = trinomialCoeff 0 1 + trinomialCoeff 0 0 ∧
      (∀ n : Nat,
        centralTrinomialNumber (Nat.succ (Nat.succ n)) =
          trinomialCoeff (Nat.succ n) (Nat.succ (Nat.succ n)) +
            trinomialCoeff (Nat.succ n) (Nat.succ n) +
              trinomialCoeff (Nat.succ n) n) := by
  constructor
  · exact centralTrinomial_zero
  · constructor
    · exact centralTrinomial_one
    · constructor
      · exact centralTrinomial_two
      · constructor
        · exact centralTrinomial_three
        · constructor
          · exact centralTrinomial_one_diagonal
          · intro n
            exact centralTrinomial_succ_succ_diagonal n

end BEDC.Derived.CentralTrinomialUp
