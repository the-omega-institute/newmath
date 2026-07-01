import BEDC.Derived.BinomialIdentitiesUp

namespace BEDC.Derived.OrderedBellNumberUp

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev finiteSum (f : Nat -> Nat) : Nat -> Nat :=
  BEDC.Derived.BinomialIdentitiesUp.finiteFoldNatSum f

def listGetD : List Nat -> Nat -> Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: tail, Nat.succ k => listGetD tail k

def indexedWeightedSum (row index : Nat) : List Nat -> Nat
  | [] => 0
  | value :: tail =>
      C row index * value + indexedWeightedSum row (Nat.succ index) tail

def orderedBellStep (values : List Nat) : List Nat :=
  values ++ [indexedWeightedSum values.length 0 values]

def orderedBellTable : Nat -> List Nat
  | 0 => [1]
  | Nat.succ n => orderedBellStep (orderedBellTable n)

def orderedBellNumber (n : Nat) : Nat :=
  listGetD (orderedBellTable n) n

abbrev fubiniNumber (n : Nat) : Nat :=
  orderedBellNumber n

theorem orderedBell_zero :
    orderedBellNumber 0 = 1 := by
  rfl

theorem orderedBell_succ (n : Nat) :
    orderedBellTable (Nat.succ n) = orderedBellStep (orderedBellTable n) := by
  rfl

theorem orderedBellStep_appends_weighted_sum (values : List Nat) :
    orderedBellStep values =
      values ++ [indexedWeightedSum values.length 0 values] := by
  rfl

theorem fubini_eq_orderedBell (n : Nat) :
    fubiniNumber n = orderedBellNumber n := by
  rfl

theorem orderedBell_one :
    orderedBellNumber 1 = 1 := by
  rfl

theorem orderedBell_two :
    orderedBellNumber 2 = 3 := by
  rfl

theorem orderedBell_three :
    orderedBellNumber 3 = 13 := by
  rfl

theorem orderedBell_four :
    orderedBellNumber 4 = 75 := by
  rfl

theorem OrderedBellNumberUp_constructive_export :
    orderedBellNumber 0 = 1 ∧
      orderedBellNumber 1 = 1 ∧
      orderedBellNumber 2 = 3 ∧
      orderedBellNumber 3 = 13 ∧
      orderedBellNumber 4 = 75 ∧
      (∀ n : Nat,
        orderedBellTable (Nat.succ n) = orderedBellStep (orderedBellTable n)) ∧
      (∀ values : List Nat,
        orderedBellStep values =
          values ++ [indexedWeightedSum values.length 0 values]) ∧
      (∀ n : Nat, fubiniNumber n = orderedBellNumber n) := by
  constructor
  · exact orderedBell_zero
  · constructor
    · exact orderedBell_one
    · constructor
      · exact orderedBell_two
      · constructor
        · exact orderedBell_three
        · constructor
          · exact orderedBell_four
          · constructor
            · intro n
              exact orderedBell_succ n
            · constructor
              · intro values
                exact orderedBellStep_appends_weighted_sum values
              · intro n
                exact fubini_eq_orderedBell n

end BEDC.Derived.OrderedBellNumberUp
