import BEDC.Algebra.FiniteFold
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.CatalanUp
import BEDC.Derived.FussCatalanUp
import BEDC.Derived.RationalUp.Core

namespace BEDC.Derived.RaneyNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_length natToUnary_unary)

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev finiteNatSum (f : Nat -> Nat) : Nat -> Nat :=
  BEDC.Derived.BinomialIdentitiesUp.finiteFoldNatSum f

abbrev IntegerUp := BEDC.Algebra.Rel.IntegerUp

def raneyDenom (m r n : Nat) : Nat :=
  m * n + r

def raneyNumerator (m r n : Nat) : Nat :=
  r * C (m * n + r) n

def raneyNumber (m r n : Nat) : Nat :=
  raneyNumerator m r n / raneyDenom m r n

def raneyExactDivision (m r n q : Nat) : Prop :=
  q * raneyDenom m r n = raneyNumerator m r n

def raneyConvolution (m r s n : Nat) : Nat :=
  finiteNatSum
    (fun i => raneyNumber m r i * raneyNumber m s (n - i)) n

def raneyFn (m r n : BHist) : BHist :=
  natToUnary (raneyNumber (bwordLength m) (bwordLength r) (bwordLength n))

def raneyInteger (m r n : Nat) : IntegerUp :=
  BEDC.Derived.RationalUp.intOfNat
    (natToUnary (raneyNumber m r n))
    (natToUnary_unary (raneyNumber m r n))

def raneyIntegerPair (m r n : Nat) : BHist × BHist :=
  BEDC.Derived.RationalUp.intToPair (raneyInteger m r n)

theorem raney_formula_surface (m r n : Nat) :
    raneyNumber m r n = r * C (m * n + r) n / (m * n + r) := by
  rfl

theorem raney_convolution_surface (m r s n : Nat) :
    raneyConvolution m r s n =
      finiteNatSum
        (fun i => raneyNumber m r i * raneyNumber m s (n - i)) n := by
  rfl

theorem raneyFn_unary_result (m r n : BHist) :
    UnaryHistory (raneyFn m r n) := by
  unfold raneyFn
  exact natToUnary_unary _

theorem raneyFn_natToUnary (m r n : Nat) :
    raneyFn (natToUnary m) (natToUnary r) (natToUnary n) =
      natToUnary (raneyNumber m r n) := by
  unfold raneyFn
  repeat rw [natToUnary_length]

theorem raneyInteger_is_bedc_integer (m r n : Nat) :
    BEDC.Derived.IntUp.IntPairCarrier
      (raneyIntegerPair m r n).1
      (raneyIntegerPair m r n).2 := by
  unfold raneyIntegerPair
  exact BEDC.Derived.RationalUp.intToPair_carrier (raneyInteger m r n)

theorem binomial_one_right (n : Nat) :
    C n 1 = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold C
      change BEDC.Derived.BinomialIdentitiesUp.C (Nat.succ n) (Nat.succ 0) =
        Nat.succ n
      change BEDC.Derived.BinomialIdentitiesUp.C n (Nat.succ 0) = n at ih
      rw [BEDC.Derived.BinomialIdentitiesUp.binomial_pascal n 0]
      rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right n]
      rw [ih]
      calc
        1 + n = n + 1 := Nat.add_comm 1 n
        _ = Nat.succ n := (Nat.succ_eq_add_one n).symm

theorem raney_r_one_zero_matches_fussCatalanCount (m : Nat) :
    raneyNumber m 1 0 =
      BEDC.Derived.FussCatalanUp.fussCatalanCount m 0 := by
  unfold raneyNumber raneyNumerator raneyDenom
  unfold BEDC.Derived.FussCatalanUp.fussCatalanCount
  unfold BEDC.Derived.FussCatalanUp.fussCatalanNumerator
  unfold BEDC.Derived.FussCatalanUp.fussCatalanDenom
  unfold C
  unfold BEDC.Derived.FussCatalanUp.C
  rw [Nat.mul_zero]
  rw [Nat.zero_add]
  rw [Nat.mul_zero]
  rw [Nat.zero_add]
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right]
  rw [BEDC.Derived.BinomialIdentitiesUp.binomial_zero_right]

theorem raney_binary_r_one_small_values :
    raneyNumber 2 1 0 = 1 ∧ raneyNumber 2 1 1 = 1 ∧
      raneyNumber 2 1 2 = 2 ∧ raneyNumber 2 1 3 = 5 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

theorem raney_binary_r_one_exact_small_values :
    raneyExactDivision 2 1 0 (raneyNumber 2 1 0) ∧
      raneyExactDivision 2 1 1 (raneyNumber 2 1 1) ∧
        raneyExactDivision 2 1 2 (raneyNumber 2 1 2) ∧
          raneyExactDivision 2 1 3 (raneyNumber 2 1 3) := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

theorem raney_binary_r_one_matches_fussCatalan_small_values :
    raneyNumber 2 1 0 = BEDC.Derived.FussCatalanUp.fussCatalanCount 2 0 ∧
      raneyNumber 2 1 1 = BEDC.Derived.FussCatalanUp.fussCatalanCount 2 1 ∧
        raneyNumber 2 1 2 = BEDC.Derived.FussCatalanUp.fussCatalanCount 2 2 ∧
          raneyNumber 2 1 3 = BEDC.Derived.FussCatalanUp.fussCatalanCount 2 3 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

theorem raney_binary_r_one_matches_CatalanUp_small_values :
    BEDC.Derived.CatalanUp.Catalan BHist.Empty
        (natToUnary (raneyNumber 2 1 0)) ∧
      BEDC.Derived.CatalanUp.Catalan (natToUnary 1)
        (natToUnary (raneyNumber 2 1 1)) ∧
        BEDC.Derived.CatalanUp.Catalan (natToUnary 2)
          (natToUnary (raneyNumber 2 1 2)) ∧
          BEDC.Derived.CatalanUp.Catalan (natToUnary 3)
            (natToUnary (raneyNumber 2 1 3)) := by
  change
    BEDC.Derived.CatalanUp.Catalan BHist.Empty (natToUnary 1) ∧
      BEDC.Derived.CatalanUp.Catalan (natToUnary 1) (natToUnary 1) ∧
        BEDC.Derived.CatalanUp.Catalan (natToUnary 2) (natToUnary 2) ∧
          BEDC.Derived.CatalanUp.Catalan (natToUnary 3) (natToUnary 5)
  constructor
  · exact BEDC.Derived.CatalanUp.catalan_zero
  · constructor
    · exact BEDC.Derived.CatalanUp.catalan_one
    · constructor
      · exact BEDC.Derived.CatalanUp.catalan_two
      · exact BEDC.Derived.CatalanUp.catalan_three

theorem raney_binary_r_one_convolution_small_values :
    raneyConvolution 2 1 1 0 = raneyNumber 2 2 0 ∧
      raneyConvolution 2 1 1 1 = raneyNumber 2 2 1 := by
  constructor
  · rfl
  · rfl

theorem RaneyNumberUp_constructive_export :
    (∀ m r n : Nat,
      raneyNumber m r n = r * C (m * n + r) n / (m * n + r)) ∧
      (∀ m : Nat,
        raneyNumber m 1 0 =
          BEDC.Derived.FussCatalanUp.fussCatalanCount m 0) ∧
      raneyNumber 2 1 0 = 1 ∧ raneyNumber 2 1 1 = 1 ∧
        raneyNumber 2 1 2 = 2 ∧ raneyNumber 2 1 3 = 5 ∧
        raneyConvolution 2 1 1 0 = raneyNumber 2 2 0 ∧
        raneyConvolution 2 1 1 1 = raneyNumber 2 2 1 ∧
        (∀ m r n : BHist, UnaryHistory (raneyFn m r n)) ∧
        (∀ m r n : Nat,
          BEDC.Derived.IntUp.IntPairCarrier
            (raneyIntegerPair m r n).1
            (raneyIntegerPair m r n).2) := by
  constructor
  · intro m r n
    exact raney_formula_surface m r n
  · constructor
    · intro m
      exact raney_r_one_zero_matches_fussCatalanCount m
    · constructor
      · exact raney_binary_r_one_small_values.left
      · constructor
        · exact raney_binary_r_one_small_values.right.left
        · constructor
          · exact raney_binary_r_one_small_values.right.right.left
          · constructor
            · exact raney_binary_r_one_small_values.right.right.right
            · constructor
              · exact raney_binary_r_one_convolution_small_values.left
              · constructor
                · exact raney_binary_r_one_convolution_small_values.right
                · constructor
                  · intro m r n
                    exact raneyFn_unary_result m r n
                  · intro m r n
                    exact raneyInteger_is_bedc_integer m r n

end BEDC.Derived.RaneyNumberUp
