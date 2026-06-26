import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.CatalanUp

namespace BEDC.Derived.NarayanaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary)

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

def narayanaNumerator (n k : Nat) : Nat :=
  C n k * C n (k - 1)

def narayanaNumber : Nat -> Nat -> Nat
  | 0, _ => 0
  | Nat.succ _, 0 => 0
  | Nat.succ n, Nat.succ k => narayanaNumerator (Nat.succ n) (Nat.succ k) / Nat.succ n

def narayanaPrefix (n : Nat) : Nat -> Nat
  | 0 => narayanaNumber n 0
  | Nat.succ k => narayanaPrefix n k + narayanaNumber n (Nat.succ k)

def narayanaRowSum (n : Nat) : Nat :=
  narayanaPrefix n n

def narayanaRowCatalanCandidate : Nat -> Nat
  | 0 => 1
  | Nat.succ n => narayanaRowSum (Nat.succ n)

def narayanaNumberFn (n k : BHist) : BHist :=
  natToUnary (narayanaNumber (bwordLength n) (bwordLength k))

def narayanaRowSumFn (n : BHist) : BHist :=
  natToUnary (narayanaRowSum (bwordLength n))

def catalanNumberFn (n : BHist) : BHist :=
  natToUnary (narayanaRowCatalanCandidate (bwordLength n))

theorem narayana_zero_left (k : Nat) :
    narayanaNumber 0 k = 0 := by
  rfl

theorem narayana_succ_formula (n k : Nat) :
    narayanaNumber (Nat.succ n) (Nat.succ k) =
      narayanaNumerator (Nat.succ n) (Nat.succ k) / Nat.succ n := by
  rfl

private theorem binomial_internal_symm (k l : Nat) :
    C (k + l) k = C (k + l) l := by
  unfold C
  induction k generalizing l with
  | zero =>
      rw [Nat.zero_add]
      rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right]
      rw [BEDC.Derived.BinomialIdentitiesUp.binomial_self]
  | succ k ihk =>
      induction l with
      | zero =>
          rw [Nat.add_zero]
          rw [BEDC.Derived.BinomialIdentitiesUp.binomial_self]
          rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right]
      | succ l ihl =>
          rw [Nat.succ_add]
          rw [Nat.add_succ]
          change BEDC.Derived.BinomialIdentitiesUp.C
              (Nat.succ (Nat.succ (k + l))) (Nat.succ k) =
            BEDC.Derived.BinomialIdentitiesUp.C
              (Nat.succ (Nat.succ (k + l))) (Nat.succ l)
          rw [BEDC.Derived.BinomialIdentitiesUp.binomial_pascal (Nat.succ (k + l)) k]
          rw [BEDC.Derived.BinomialIdentitiesUp.binomial_pascal (Nat.succ (k + l)) l]
          have leftSymm := ihk (Nat.succ l)
          rw [Nat.add_succ] at leftSymm
          have leftSlot :
              BEDC.Derived.BinomialIdentitiesUp.C (Nat.succ (k + l)) k =
                BEDC.Derived.BinomialIdentitiesUp.C
                  (Nat.succ (k + l)) (Nat.succ l) :=
            leftSymm
          have rightSymm := ihl
          rw [Nat.succ_add] at rightSymm
          have rightSlot :
              BEDC.Derived.BinomialIdentitiesUp.C
                  (Nat.succ (k + l)) (Nat.succ k) =
                BEDC.Derived.BinomialIdentitiesUp.C (Nat.succ (k + l)) l :=
            rightSymm
          rw [leftSlot, rightSlot]
          exact Nat.add_comm _ _

theorem binomial_complement_symmetry (k l : Nat) :
    C (k + l) k = C (k + l) l :=
  binomial_internal_symm k l

theorem narayana_complement_symmetry (k l : Nat) :
    narayanaNumber (Nat.succ (k + l)) (Nat.succ k) =
      narayanaNumber (Nat.succ (k + l)) (Nat.succ l) := by
  rw [narayana_succ_formula, narayana_succ_formula]
  unfold narayanaNumerator
  have chooseLeft := binomial_internal_symm (Nat.succ k) l
  rw [Nat.succ_add] at chooseLeft
  have chooseRight := binomial_internal_symm k (Nat.succ l)
  rw [Nat.add_succ] at chooseRight
  change C (Nat.succ (k + l)) (Nat.succ k) * C (Nat.succ (k + l)) k /
      Nat.succ (k + l) =
    C (Nat.succ (k + l)) (Nat.succ l) * C (Nat.succ (k + l)) l /
      Nat.succ (k + l)
  rw [chooseLeft, chooseRight]
  rw [Nat.mul_comm]

theorem narayana_left_boundary (n : Nat) :
    narayanaNumber (Nat.succ n) 0 = 0 := by
  rfl

theorem narayana_one_one :
    narayanaNumber 1 1 = 1 := by
  rfl

theorem narayana_two_row :
    narayanaNumber 2 1 = 1 ∧ narayanaNumber 2 2 = 1 := by
  constructor <;> rfl

theorem narayana_three_row :
    narayanaNumber 3 1 = 1 ∧ narayanaNumber 3 2 = 3 ∧
      narayanaNumber 3 3 = 1 := by
  constructor
  · rfl
  · constructor <;> rfl

theorem narayana_row_sum_zero :
    narayanaRowSum 0 = 0 := by
  rfl

theorem narayana_row_sum_one :
    narayanaRowSum 1 = 1 := by
  rfl

theorem narayana_row_sum_two :
    narayanaRowSum 2 = 2 := by
  rfl

theorem narayana_row_sum_three :
    narayanaRowSum 3 = 5 := by
  rfl

theorem catalan_small_values :
    BEDC.Derived.CatalanUp.Catalan BHist.Empty (natToUnary 1) ∧
      BEDC.Derived.CatalanUp.Catalan (natToUnary 1) (natToUnary 1) ∧
        BEDC.Derived.CatalanUp.Catalan (natToUnary 2) (natToUnary 2) ∧
          BEDC.Derived.CatalanUp.Catalan (natToUnary 3) (natToUnary 5) := by
  constructor
  · exact BEDC.Derived.CatalanUp.catalan_zero
  · constructor
    · exact BEDC.Derived.CatalanUp.catalan_one
    · constructor
      · exact BEDC.Derived.CatalanUp.catalan_two
      · exact BEDC.Derived.CatalanUp.catalan_three

theorem narayana_row_sum_matches_CatalanUp_small :
    BEDC.Derived.CatalanUp.Catalan (natToUnary 1) (natToUnary (narayanaRowSum 1)) ∧
      BEDC.Derived.CatalanUp.Catalan (natToUnary 2) (natToUnary (narayanaRowSum 2)) ∧
        BEDC.Derived.CatalanUp.Catalan (natToUnary 3) (natToUnary (narayanaRowSum 3)) := by
  change
    BEDC.Derived.CatalanUp.Catalan (natToUnary 1) (natToUnary 1) ∧
      BEDC.Derived.CatalanUp.Catalan (natToUnary 2) (natToUnary 2) ∧
        BEDC.Derived.CatalanUp.Catalan (natToUnary 3) (natToUnary 5)
  constructor
  · exact BEDC.Derived.CatalanUp.catalan_one
  · constructor
    · exact BEDC.Derived.CatalanUp.catalan_two
    · exact BEDC.Derived.CatalanUp.catalan_three

theorem narayanaNumberFn_unary_result (n k : BHist) :
    UnaryHistory (narayanaNumberFn n k) := by
  unfold narayanaNumberFn
  exact natToUnary_unary _

theorem narayanaRowSumFn_unary_result (n : BHist) :
    UnaryHistory (narayanaRowSumFn n) := by
  unfold narayanaRowSumFn
  exact natToUnary_unary _

theorem catalanNumberFn_unary_result (n : BHist) :
    UnaryHistory (catalanNumberFn n) := by
  unfold catalanNumberFn
  exact natToUnary_unary _

theorem NarayanaUp_constructive_export :
    (∀ k : Nat, narayanaNumber 0 k = 0) ∧
      (∀ n : Nat, narayanaNumber (Nat.succ n) 0 = 0) ∧
      (∀ n k : Nat, narayanaNumber (Nat.succ n) (Nat.succ k) =
        narayanaNumerator (Nat.succ n) (Nat.succ k) / Nat.succ n) ∧
      (∀ k l : Nat, narayanaNumber (Nat.succ (k + l)) (Nat.succ k) =
        narayanaNumber (Nat.succ (k + l)) (Nat.succ l)) ∧
      narayanaRowSum 1 = 1 ∧ narayanaRowSum 2 = 2 ∧ narayanaRowSum 3 = 5 ∧
        BEDC.Derived.CatalanUp.Catalan (natToUnary 1) (natToUnary (narayanaRowSum 1)) ∧
          BEDC.Derived.CatalanUp.Catalan (natToUnary 2) (natToUnary (narayanaRowSum 2)) ∧
            BEDC.Derived.CatalanUp.Catalan (natToUnary 3) (natToUnary (narayanaRowSum 3)) := by
  constructor
  · intro k
    exact narayana_zero_left k
  · constructor
    · intro n
      exact narayana_left_boundary n
    · constructor
      · intro n k
        exact narayana_succ_formula n k
      · constructor
        · intro k l
          exact narayana_complement_symmetry k l
        · constructor
          · exact narayana_row_sum_one
          · constructor
            · exact narayana_row_sum_two
            · constructor
              · exact narayana_row_sum_three
              · exact narayana_row_sum_matches_CatalanUp_small

end BEDC.Derived.NarayanaUp
