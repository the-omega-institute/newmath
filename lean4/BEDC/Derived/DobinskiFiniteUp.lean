import BEDC.Derived.BellNumberUp
import BEDC.Derived.PartialBellUp

namespace BEDC.Derived.DobinskiFiniteUp

abbrev stirlingSecond : Nat -> Nat -> Nat :=
  BEDC.Derived.StirlingUp.stirlingSecond

abbrev bellNumber : Nat -> Nat :=
  BEDC.Derived.BellNumberUp.bellNumber

abbrev recurrenceBellNumber : Nat -> Nat :=
  BEDC.Derived.BellNumberUp.bellNumberByRecurrence

abbrev chooseCount : Nat -> Nat -> Nat :=
  BEDC.Derived.BellNumberUp.natChooseCount

def inclusiveRange : Nat -> List Nat
  | 0 => [0]
  | Nat.succ n => inclusiveRange n ++ [Nat.succ n]

def listNatSum (f : Nat -> Nat) : List Nat -> Nat
  | [] => 0
  | k :: ks => f k + listNatSum f ks

def finiteDobinskiStirlingPrefix (n : Nat) : Nat -> Nat
  | 0 => stirlingSecond n 0
  | Nat.succ k =>
      finiteDobinskiStirlingPrefix n k + stirlingSecond n (Nat.succ k)

def finiteDobinskiStirlingSum (n : Nat) : Nat :=
  finiteDobinskiStirlingPrefix n n

def bellTriangleEntry (n k : Nat) : Nat :=
  BEDC.Derived.BellNumberUp.bellRecurrencePrefix recurrenceBellNumber n k

def bellTriangleLast (n : Nat) : Nat :=
  bellTriangleEntry n n

def bellTriangleRowPrefix (n : Nat) : Nat -> List Nat
  | 0 => [bellTriangleEntry n 0]
  | Nat.succ k => bellTriangleRowPrefix n k ++ [bellTriangleEntry n (Nat.succ k)]

def bellTriangleRow (n : Nat) : List Nat :=
  bellTriangleRowPrefix n n

theorem listNatSum_append (f : Nat -> Nat) :
    forall xs ys : List Nat,
      listNatSum f (xs ++ ys) = listNatSum f xs + listNatSum f ys
  | [], ys => by
      change listNatSum f ys = 0 + listNatSum f ys
      exact (Nat.zero_add (listNatSum f ys)).symm
  | x :: xs, ys => by
      change f x + listNatSum f (xs ++ ys) =
        (f x + listNatSum f xs) + listNatSum f ys
      rw [listNatSum_append f xs ys]
      exact (Nat.add_assoc (f x) (listNatSum f xs) (listNatSum f ys)).symm

theorem listNatSum_singleton (f : Nat -> Nat) (k : Nat) :
    listNatSum f [k] = f k := by
  change f k + 0 = f k
  exact Nat.add_zero (f k)

theorem finiteDobinskiStirlingPrefix_list_sum (n : Nat) :
    forall k : Nat,
      listNatSum (stirlingSecond n) (inclusiveRange k) =
        finiteDobinskiStirlingPrefix n k
  | 0 => by
      rfl
  | Nat.succ k => by
      change
        listNatSum (stirlingSecond n) (inclusiveRange k ++ [Nat.succ k]) =
          finiteDobinskiStirlingPrefix n k + stirlingSecond n (Nat.succ k)
      rw [listNatSum_append]
      rw [finiteDobinskiStirlingPrefix_list_sum n k]
      rw [listNatSum_singleton]

theorem finiteDobinskiStirlingPrefix_bellPrefix (n : Nat) :
    forall k : Nat,
      finiteDobinskiStirlingPrefix n k =
        BEDC.Derived.BellNumberUp.bellStirlingPrefix n k
  | 0 => by
      rfl
  | Nat.succ k => by
      change finiteDobinskiStirlingPrefix n k + stirlingSecond n (Nat.succ k) =
        BEDC.Derived.BellNumberUp.bellStirlingPrefix n k +
          stirlingSecond n (Nat.succ k)
      rw [finiteDobinskiStirlingPrefix_bellPrefix n k]

theorem finiteDobinskiStirlingSum_definition (n : Nat) :
    finiteDobinskiStirlingSum n = finiteDobinskiStirlingPrefix n n := by
  rfl

theorem finiteDobinskiStirlingSum_list_sum (n : Nat) :
    finiteDobinskiStirlingSum n =
      listNatSum (stirlingSecond n) (inclusiveRange n) := by
  unfold finiteDobinskiStirlingSum
  exact (finiteDobinskiStirlingPrefix_list_sum n n).symm

theorem bellNumber_stirling_sum (n : Nat) :
    bellNumber n = finiteDobinskiStirlingSum n := by
  unfold bellNumber finiteDobinskiStirlingSum
  exact (finiteDobinskiStirlingPrefix_bellPrefix n n).symm

theorem bellNumber_list_stirling_sum (n : Nat) :
    bellNumber n = listNatSum (stirlingSecond n) (inclusiveRange n) := by
  rw [bellNumber_stirling_sum n]
  exact finiteDobinskiStirlingSum_list_sum n

theorem partialBell_allOnes_stirlingSecond (n k : Nat) :
    BEDC.Derived.PartialBellUp.partialBell (fun _ => 1) n k =
      stirlingSecond n k := by
  exact BEDC.Derived.PartialBellUp.partialBell_allOnes_stirlingSecond n k

theorem completeBell_allOnes_bellNumber (n : Nat) :
    BEDC.Derived.PartialBellUp.completeBell (fun _ => 1) n = bellNumber n := by
  exact BEDC.Derived.PartialBellUp.partialBell_completeBell n

theorem completeBell_allOnes_stirling_sum (n : Nat) :
    BEDC.Derived.PartialBellUp.completeBell (fun _ => 1) n =
      finiteDobinskiStirlingSum n := by
  rw [completeBell_allOnes_bellNumber n]
  exact bellNumber_stirling_sum n

theorem recurrenceBellNumber_recurrence (n : Nat) :
    recurrenceBellNumber (Nat.succ n) =
      BEDC.Derived.BellNumberUp.bellRecurrencePrefix recurrenceBellNumber n n := by
  exact BEDC.Derived.BellNumberUp.bellNumberByRecurrence_standard_recurrence n

theorem recurrenceBellNumber_choose_sum (n : Nat) :
    recurrenceBellNumber (Nat.succ n) = bellTriangleEntry n n := by
  exact recurrenceBellNumber_recurrence n

theorem bellTriangleEntry_zero (n : Nat) :
    bellTriangleEntry n 0 = chooseCount n 0 * recurrenceBellNumber 0 := by
  rfl

theorem bellTriangleEntry_succ (n k : Nat) :
    bellTriangleEntry n (Nat.succ k) =
      bellTriangleEntry n k + chooseCount n (Nat.succ k) *
        recurrenceBellNumber (Nat.succ k) := by
  rfl

theorem bellTriangleLast_definition (n : Nat) :
    bellTriangleLast n = bellTriangleEntry n n := by
  rfl

theorem bellTriangle_next_row_last (n : Nat) :
    bellTriangleLast n = recurrenceBellNumber (Nat.succ n) := by
  unfold bellTriangleLast
  exact (recurrenceBellNumber_choose_sum n).symm

theorem bellTriangleRowPrefix_succ (n k : Nat) :
    bellTriangleRowPrefix n (Nat.succ k) =
      bellTriangleRowPrefix n k ++ [bellTriangleEntry n (Nat.succ k)] := by
  rfl

theorem bellTriangleRow_definition (n : Nat) :
    bellTriangleRow n = bellTriangleRowPrefix n n := by
  rfl

theorem finiteDobinski_small_values :
    bellNumber 0 = 1 ∧ bellNumber 1 = 1 ∧
      bellNumber 2 = 2 ∧ bellNumber 3 = 5 ∧ bellNumber 4 = 15 := by
  constructor
  · exact BEDC.Derived.BellNumberUp.bellNumber_zero
  · constructor
    · exact BEDC.Derived.BellNumberUp.bellNumber_one
    · constructor
      · exact BEDC.Derived.BellNumberUp.bellNumber_two
      · constructor
        · exact BEDC.Derived.BellNumberUp.bellNumber_three
        · exact BEDC.Derived.BellNumberUp.bellNumber_four

theorem DobinskiFiniteUp_constructive_export :
    (∀ n : Nat,
      bellNumber n = listNatSum (stirlingSecond n) (inclusiveRange n)) ∧
      (∀ n k : Nat,
        BEDC.Derived.PartialBellUp.partialBell (fun _ => 1) n k =
          stirlingSecond n k) ∧
      (∀ n : Nat,
        BEDC.Derived.PartialBellUp.completeBell (fun _ => 1) n =
          finiteDobinskiStirlingSum n) ∧
      (∀ n : Nat,
        recurrenceBellNumber (Nat.succ n) =
          BEDC.Derived.BellNumberUp.bellRecurrencePrefix recurrenceBellNumber n n) ∧
      (∀ n : Nat, bellTriangleLast n = recurrenceBellNumber (Nat.succ n)) := by
  constructor
  · intro n
    exact bellNumber_list_stirling_sum n
  · constructor
    · intro n k
      exact partialBell_allOnes_stirlingSecond n k
    · constructor
      · intro n
        exact completeBell_allOnes_stirling_sum n
      · constructor
        · intro n
          exact recurrenceBellNumber_recurrence n
        · intro n
          exact bellTriangle_next_row_last n

end BEDC.Derived.DobinskiFiniteUp
