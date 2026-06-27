import BEDC.Algebra.FiniteFold
import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.CatalanUp
import BEDC.Derived.FussCatalanUp
import BEDC.Derived.IntUp
import BEDC.Derived.LobbUp

namespace BEDC.Derived.CatalanConvolutionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_length natToUnary_unary)

abbrev C (n k : Nat) : Nat :=
  BEDC.Derived.BinomialIdentitiesUp.C n k

abbrev finiteNatSum (f : Nat -> Nat) : Nat -> Nat :=
  BEDC.Derived.BinomialIdentitiesUp.finiteFoldNatSum f

def natRange : Nat -> List Nat
  | 0 => [0]
  | Nat.succ n => natRange n ++ [Nat.succ n]

def listNatSum : List Nat -> Nat
  | [] => 0
  | x :: xs => x + listNatSum xs

def listNthD : List Nat -> Nat -> Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, Nat.succ n => listNthD xs n

def listLen : List Nat -> Nat
  | [] => 0
  | _ :: xs => Nat.succ (listLen xs)

def finiteFoldBounded (n : Nat) (f : (i : Nat) -> i ≤ n -> Nat) : Nat :=
  match n with
  | 0 => f 0 (Nat.le_refl 0)
  | Nat.succ k =>
      finiteFoldBounded k (fun i hi => f i (Nat.le_trans hi (Nat.le_succ k))) +
        f (Nat.succ k) (Nat.le_refl (Nat.succ k))

def catalanPrefixConvolution (pref : List Nat) (n : Nat) : Nat :=
  listNatSum ((natRange n).map
    (fun i => listNthD pref i * listNthD pref (n - i)))

def catalanPrefix : Nat -> List Nat
  | 0 => [1]
  | Nat.succ n =>
      catalanPrefix n ++
        [catalanPrefixConvolution (catalanPrefix n) n]

def catalanNumber (n : Nat) : Nat :=
  listNthD (catalanPrefix n) n

def catalanConvolutionSum (n : Nat) : Nat :=
  catalanPrefixConvolution (catalanPrefix n) n

def catalanBinomialDivision (n : Nat) : Nat :=
  C (n + n) n / (n + 1)

def catalanBinomialDifference (n : Nat) : Nat :=
  C (n + n) n - C (n + n) (Nat.succ n)

def catalanNumberFn (n : BHist) : BHist :=
  natToUnary (catalanNumber (bwordLength n))

def catalanConvolutionSumFn (n : BHist) : BHist :=
  natToUnary (catalanConvolutionSum (bwordLength n))

theorem listLen_append_singleton (xs : List Nat) (x : Nat) :
    listLen (xs ++ [x]) = Nat.succ (listLen xs) := by
  induction xs with
  | nil => rfl
  | cons _ ys ih =>
      exact congrArg Nat.succ ih

theorem listNthD_append_at_listLen (xs : List Nat) (x : Nat) :
    listNthD (xs ++ [x]) (listLen xs) = x := by
  induction xs with
  | nil => rfl
  | cons _ ys ih =>
      exact ih

theorem catalanPrefix_listLen (n : Nat) :
    listLen (catalanPrefix n) = Nat.succ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact Eq.trans
        (listLen_append_singleton (catalanPrefix n)
          (catalanPrefixConvolution (catalanPrefix n) n))
        (congrArg Nat.succ ih)

theorem listNthD_append_at_succ_of_listLen (xs : List Nat) (x n : Nat)
    (h : listLen xs = Nat.succ n) :
    listNthD (xs ++ [x]) (Nat.succ n) = x := by
  exact Eq.ndrec (motive := fun k => listNthD (xs ++ [x]) k = x)
    (listNthD_append_at_listLen xs x) h

theorem catalan_zero :
    catalanNumber 0 = 1 := by
  rfl

theorem catalan_succ_segner (n : Nat) :
    catalanNumber (Nat.succ n) = catalanConvolutionSum n := by
  exact listNthD_append_at_succ_of_listLen
    (catalanPrefix n)
    (catalanPrefixConvolution (catalanPrefix n) n)
    n
    (catalanPrefix_listLen n)

theorem segner_convolution (n : Nat) :
    catalanConvolutionSum n = catalanNumber (Nat.succ n) := by
  exact (catalan_succ_segner n).symm

theorem catalan_binomial_division_surface (n : Nat) :
    catalanBinomialDivision n = C (n + n) n / (n + 1) := by
  rfl

theorem catalan_binomial_difference_surface (n : Nat) :
    catalanBinomialDifference n = C (n + n) n - C (n + n) (Nat.succ n) := by
  rfl

theorem catalan_difference_matches_lobb (n : Nat) :
    catalanBinomialDifference n = BEDC.Derived.LobbUp.catalanNat n := by
  rfl

theorem catalan_division_matches_binary_fuss (n : Nat) :
    catalanBinomialDivision n = BEDC.Derived.FussCatalanUp.fussCatalanCount 2 n := by
  unfold catalanBinomialDivision
  unfold BEDC.Derived.FussCatalanUp.fussCatalanCount
  unfold BEDC.Derived.FussCatalanUp.fussCatalanNumerator
  unfold BEDC.Derived.FussCatalanUp.fussCatalanDenom
  rw [Nat.one_mul]
  rw [Nat.two_mul]

theorem catalanNumberFn_unary_result (n : BHist) :
    UnaryHistory (catalanNumberFn n) := by
  unfold catalanNumberFn
  exact natToUnary_unary _

theorem catalanConvolutionSumFn_unary_result (n : BHist) :
    UnaryHistory (catalanConvolutionSumFn n) := by
  unfold catalanConvolutionSumFn
  exact natToUnary_unary _

theorem catalanNumberFn_natToUnary (n : Nat) :
    catalanNumberFn (natToUnary n) = natToUnary (catalanNumber n) := by
  unfold catalanNumberFn
  rw [natToUnary_length]

theorem catalanConvolutionSumFn_natToUnary (n : Nat) :
    catalanConvolutionSumFn (natToUnary n) =
      natToUnary (catalanConvolutionSum n) := by
  unfold catalanConvolutionSumFn
  rw [natToUnary_length]

theorem catalan_binomial_division_small_values :
    catalanBinomialDivision 0 = 1 ∧ catalanBinomialDivision 1 = 1 ∧
      catalanBinomialDivision 2 = 2 ∧ catalanBinomialDivision 3 = 5 ∧
        catalanBinomialDivision 4 = 14 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · rfl

theorem catalan_binomial_difference_small_values :
    catalanBinomialDifference 0 = 1 ∧ catalanBinomialDifference 1 = 1 ∧
      catalanBinomialDifference 2 = 2 ∧ catalanBinomialDifference 3 = 5 ∧
        catalanBinomialDifference 4 = 14 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · rfl

theorem CatalanConvolutionUp_constructive_export :
    catalanNumber 0 = 1 ∧
      (∀ n : Nat, catalanConvolutionSum n = catalanNumber (Nat.succ n)) ∧
      (∀ n : Nat, catalanBinomialDivision n = C (n + n) n / (n + 1)) ∧
      (∀ n : Nat,
        catalanBinomialDifference n = C (n + n) n - C (n + n) (Nat.succ n)) ∧
      (∀ n : Nat,
        catalanBinomialDifference n = BEDC.Derived.LobbUp.catalanNat n) ∧
      (∀ n : Nat,
        catalanBinomialDivision n = BEDC.Derived.FussCatalanUp.fussCatalanCount 2 n) ∧
      catalanBinomialDivision 4 = 14 ∧
        catalanBinomialDifference 4 = 14 ∧
        (∀ n : BHist, UnaryHistory (catalanNumberFn n)) ∧
        (∀ n : BHist, UnaryHistory (catalanConvolutionSumFn n)) := by
  constructor
  · exact catalan_zero
  · constructor
    · intro n
      exact segner_convolution n
    · constructor
      · intro n
        exact catalan_binomial_division_surface n
      · constructor
        · intro n
          exact catalan_binomial_difference_surface n
        · constructor
          · intro n
            exact catalan_difference_matches_lobb n
          · constructor
            · intro n
              exact catalan_division_matches_binary_fuss n
            · constructor
              · exact catalan_binomial_division_small_values.right.right.right.right
              · constructor
                · exact catalan_binomial_difference_small_values.right.right.right.right
                · constructor
                  · intro n
                    exact catalanNumberFn_unary_result n
                  · intro n
                    exact catalanConvolutionSumFn_unary_result n

end BEDC.Derived.CatalanConvolutionUp
