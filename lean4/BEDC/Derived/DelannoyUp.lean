import BEDC.Algebra.FiniteFold
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.CatalanUp

namespace BEDC.Derived.DelannoyUp

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

def delannoyRowStep (previous : Nat -> Nat) : Nat -> Nat
  | 0 => 1
  | Nat.succ n => previous (Nat.succ n) + delannoyRowStep previous n + previous n

def delannoyNumber : Nat -> Nat -> Nat
  | 0, _ => 1
  | Nat.succ m, n => delannoyRowStep (delannoyNumber m) n

def centralDelannoyNumber (n : Nat) : Nat :=
  delannoyNumber n n

def rangeFuel : Nat -> List Nat
  | 0 => [0]
  | Nat.succ fuel => rangeFuel fuel ++ [Nat.succ fuel]

def natListSum : List Nat -> Nat
  | [] => 0
  | x :: xs => x + natListSum xs

def delannoyClosedFormTerm (m n k : Nat) : Nat :=
  C m k * C n k * 2 ^ k

def delannoyClosedFormWithFuel (m n fuel : Nat) : Nat :=
  natListSum (List.map (delannoyClosedFormTerm m n) (rangeFuel fuel))

def delannoyClosedForm (m n : Nat) : Nat :=
  delannoyClosedFormWithFuel m n (m + n)

theorem delannoy_left_boundary (n : Nat) :
    delannoyNumber 0 n = 1 := by
  rfl

theorem delannoy_bottom_boundary :
    ∀ m : Nat, delannoyNumber m 0 = 1
  | 0 => by
      rfl
  | Nat.succ _m => by
      rfl

theorem delannoy_recurrence (m n : Nat) :
    delannoyNumber (Nat.succ m) (Nat.succ n) =
      delannoyNumber m (Nat.succ n) +
        delannoyNumber (Nat.succ m) n +
          delannoyNumber m n := by
  rfl

theorem central_delannoy_def (n : Nat) :
    centralDelannoyNumber n = delannoyNumber n n := by
  rfl

theorem rangeFuel_zero :
    rangeFuel 0 = [0] := by
  rfl

theorem rangeFuel_succ (fuel : Nat) :
    rangeFuel (Nat.succ fuel) = rangeFuel fuel ++ [Nat.succ fuel] := by
  rfl

theorem natListSum_nil :
    natListSum [] = 0 := by
  rfl

theorem natListSum_cons (x : Nat) (xs : List Nat) :
    natListSum (x :: xs) = x + natListSum xs := by
  rfl

theorem delannoyClosedFormWithFuel_zero (m n : Nat) :
    delannoyClosedFormWithFuel m n 0 =
      delannoyClosedFormTerm m n 0 := by
  rfl

theorem delannoyClosedFormWithFuel_succ (m n fuel : Nat) :
    delannoyClosedFormWithFuel m n (Nat.succ fuel) =
      natListSum
        (List.map (delannoyClosedFormTerm m n)
          (rangeFuel fuel ++ [Nat.succ fuel])) := by
  rfl

theorem delannoy_small_values :
    delannoyNumber 0 0 = 1 ∧
      delannoyNumber 1 0 = 1 ∧
        delannoyNumber 0 1 = 1 ∧
          delannoyNumber 1 1 = 3 ∧
            delannoyNumber 2 1 = 5 ∧
              delannoyNumber 2 2 = 13 := by
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

theorem delannoyClosedForm_small_values :
    delannoyClosedForm 0 0 = delannoyNumber 0 0 ∧
      delannoyClosedForm 1 0 = delannoyNumber 1 0 ∧
        delannoyClosedForm 0 1 = delannoyNumber 0 1 ∧
          delannoyClosedForm 1 1 = delannoyNumber 1 1 ∧
            delannoyClosedForm 2 1 = delannoyNumber 2 1 ∧
              delannoyClosedForm 2 2 = delannoyNumber 2 2 := by
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

theorem central_delannoy_small_values :
    centralDelannoyNumber 0 = 1 ∧
      centralDelannoyNumber 1 = 3 ∧
        centralDelannoyNumber 2 = 13 := by
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

theorem DelannoyUp_constructive_export :
    (∀ n : Nat, delannoyNumber 0 n = 1) ∧
      (∀ m : Nat, delannoyNumber m 0 = 1) ∧
      (∀ m n : Nat,
        delannoyNumber (Nat.succ m) (Nat.succ n) =
          delannoyNumber m (Nat.succ n) +
            delannoyNumber (Nat.succ m) n +
              delannoyNumber m n) ∧
      (∀ n : Nat, centralDelannoyNumber n = delannoyNumber n n) ∧
      delannoyClosedForm 0 0 = delannoyNumber 0 0 ∧
        delannoyClosedForm 1 1 = delannoyNumber 1 1 ∧
          delannoyClosedForm 2 2 = delannoyNumber 2 2 := by
  constructor
  · intro n
    exact delannoy_left_boundary n
  · constructor
    · intro m
      exact delannoy_bottom_boundary m
    · constructor
      · intro m n
        exact delannoy_recurrence m n
      · constructor
        · intro n
          exact central_delannoy_def n
        · constructor
          · exact delannoyClosedForm_small_values.left
          · constructor
            · exact delannoyClosedForm_small_values.right.right.right.left
            · exact delannoyClosedForm_small_values.right.right.right.right.right

end BEDC.Derived.DelannoyUp
