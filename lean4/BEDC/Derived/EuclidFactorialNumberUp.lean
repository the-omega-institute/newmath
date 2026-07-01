namespace BEDC.Derived.EuclidFactorialNumberUp

def factorialNat : Nat -> Nat
  | 0 => 1
  | Nat.succ n => Nat.succ n * factorialNat n

def euclidFactorialNumber (n : Nat) : Nat :=
  factorialNat n + 1

def euclidFactorialPrefix : Nat -> List Nat
  | 0 => []
  | Nat.succ n => euclidFactorialPrefix n ++ [euclidFactorialNumber n]

theorem factorialNat_zero :
    factorialNat 0 = 1 := by
  rfl

theorem factorialNat_succ (n : Nat) :
    factorialNat (Nat.succ n) = Nat.succ n * factorialNat n := by
  rfl

theorem euclidFactorialNumber_zero :
    euclidFactorialNumber 0 = 2 := by
  rfl

theorem euclidFactorialNumber_succ (n : Nat) :
    euclidFactorialNumber (Nat.succ n) =
      Nat.succ n * factorialNat n + 1 := by
  rfl

theorem factorialNat_small_values :
    factorialNat 0 = 1 ∧
      factorialNat 1 = 1 ∧
      factorialNat 2 = 2 ∧
      factorialNat 3 = 6 ∧
      factorialNat 4 = 24 ∧
      factorialNat 5 = 120 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · rfl

theorem euclidFactorialNumber_small_values :
    euclidFactorialNumber 0 = 2 ∧
      euclidFactorialNumber 1 = 2 ∧
      euclidFactorialNumber 2 = 3 ∧
      euclidFactorialNumber 3 = 7 ∧
      euclidFactorialNumber 4 = 25 ∧
      euclidFactorialNumber 5 = 121 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · rfl

theorem euclidFactorialPrefix_five :
    euclidFactorialPrefix 5 = [2, 2, 3, 7, 25] := by
  rfl

theorem EuclidFactorialNumberUp_constructive_export :
    factorialNat 0 = 1 ∧
      (∀ n : Nat, factorialNat (Nat.succ n) =
        Nat.succ n * factorialNat n) ∧
      (∀ n : Nat, euclidFactorialNumber (Nat.succ n) =
        Nat.succ n * factorialNat n + 1) ∧
      euclidFactorialPrefix 5 = [2, 2, 3, 7, 25] ∧
      euclidFactorialNumber 5 = 121 := by
  constructor
  · exact factorialNat_zero
  · constructor
    · intro n
      exact factorialNat_succ n
    · constructor
      · intro n
        exact euclidFactorialNumber_succ n
      · constructor
        · exact euclidFactorialPrefix_five
        · rfl

end BEDC.Derived.EuclidFactorialNumberUp
