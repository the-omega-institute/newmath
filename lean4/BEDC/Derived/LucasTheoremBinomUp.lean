import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.PrimeUp.DividesClosure

namespace BEDC.Derived.LucasTheoremBinomUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.BinomialIdentitiesUp
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length natMulFn
  natMulFn_rel)
open BEDC.Derived.PrimeUp

abbrev Binom (m n : Nat) : Nat :=
  C m n

def NatModEq (p a b : Nat) : Prop :=
  ∃ u v : Nat, a + p * u = b + p * v

theorem NatModEq_refl (p a : Nat) :
    NatModEq p a a := by
  exact ⟨0, 0, rfl⟩

theorem NatModEq_symm {p a b : Nat} :
    NatModEq p a b -> NatModEq p b a := by
  intro h
  cases h with
  | intro u rest =>
      cases rest with
      | intro v eqn =>
          exact ⟨v, u, eqn.symm⟩

def baseDigitBump (p : Nat) : List Nat -> List Nat
  | [] => [1]
  | d :: ds =>
      if d + 1 = p then
        0 :: baseDigitBump p ds
      else
        (d + 1) :: ds

def baseDigits (p : Nat) : Nat -> List Nat
  | 0 => []
  | Nat.succ n => baseDigitBump p (baseDigits p n)

def digitEval (p : Nat) : List Nat -> Nat
  | [] => 0
  | d :: ds => d + p * digitEval p ds

def digitBinomProductNilLeft : List Nat -> Nat
  | [] => 1
  | n :: ns => C 0 n * digitBinomProductNilLeft ns

def digitBinomProduct : List Nat -> List Nat -> Nat
  | [], ns => digitBinomProductNilLeft ns
  | m :: ms, [] => C m 0 * digitBinomProduct ms []
  | m :: ms, n :: ns => C m n * digitBinomProduct ms ns

def lucasDigitProduct (p m n : Nat) : Nat :=
  digitBinomProduct (baseDigits p m) (baseDigits p n)

private theorem nat_add_succ_rotate (a d : Nat) :
    a + (d + 1) = d + a + 1 := by
  calc
    a + (d + 1) = a + d + 1 := (Nat.add_assoc a d 1).symm
    _ = d + a + 1 := congrArg (fun t => t + 1) (Nat.add_comm a d)

private theorem nat_mul_succ_digit (p d x : Nat) :
    d + 1 = p -> p * (x + 1) = d + p * x + 1 := by
  intro h
  rw [Nat.mul_succ]
  rw [h.symm]
  exact nat_add_succ_rotate ((d + 1) * x) d

private theorem digitEval_bump (p : Nat) :
    ∀ ds : List Nat, digitEval p (baseDigitBump p ds) =
      digitEval p ds + 1
  | [] => by
      rfl
  | d :: ds => by
      by_cases h : d + 1 = p
      · unfold baseDigitBump digitEval
        rw [if_pos h]
        change 0 + p * digitEval p (baseDigitBump p ds) =
          d + p * digitEval p ds + 1
        rw [Nat.zero_add]
        rw [digitEval_bump p ds]
        exact nat_mul_succ_digit p d (digitEval p ds) h
      · unfold baseDigitBump digitEval
        rw [if_neg h]
        calc
          d + 1 + p * digitEval p ds =
              d + (1 + p * digitEval p ds) := Nat.add_assoc d 1 (p * digitEval p ds)
          _ = d + (p * digitEval p ds + 1) :=
            congrArg (fun x => d + x) (Nat.add_comm 1 (p * digitEval p ds))
          _ = d + p * digitEval p ds + 1 :=
            (Nat.add_assoc d (p * digitEval p ds) 1).symm

theorem digitEval_baseDigits (p n : Nat) :
    digitEval p (baseDigits p n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold baseDigits
      rw [digitEval_bump]
      rw [ih]

theorem digitBinomProduct_nil_right (ds : List Nat) :
    digitBinomProduct ds [] = 1 := by
  induction ds with
  | nil =>
      unfold digitBinomProduct
      rfl
  | cons d ds ih =>
      unfold digitBinomProduct
      rw [binomial_zero_right d]
      rw [ih]

theorem lucasDigitProduct_zero_right (p m : Nat) :
    lucasDigitProduct p m 0 = 1 := by
  unfold lucasDigitProduct
  exact digitBinomProduct_nil_right (baseDigits p m)

theorem lucasDigitProduct_zero_zero (p : Nat) :
    lucasDigitProduct p 0 0 = 1 := by
  exact lucasDigitProduct_zero_right p 0

private theorem natToUnary_append_local (m n : Nat) :
    append (natToUnary m) (natToUnary n) = natToUnary (m + n) := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ n ih =>
      change BHist.e1 (append (natToUnary m) (natToUnary n)) =
        natToUnary (m + Nat.succ n)
      rw [ih]
      rw [Nat.add_succ]
      rfl

private theorem natMulFn_natToUnary_local (m n : Nat) :
    natMulFn (natToUnary m) (natToUnary n) = natToUnary (m * n) := by
  induction n with
  | zero =>
      rw [Nat.mul_zero]
      rfl
  | succ n ih =>
      change append (natMulFn (natToUnary m) (natToUnary n)) (natToUnary m) =
        natToUnary (m * Nat.succ n)
      rw [ih]
      rw [natToUnary_append_local]
      rw [Nat.mul_succ]

def NatDvd (p n : Nat) : Prop :=
  NatDivides (natToUnary p) (natToUnary n)

def NatPrimeUp (p : Nat) : Prop :=
  NatPrime (natToUnary p)

theorem NatDvd_of_factor {p n q : Nat} :
    n = p * q -> NatDvd p n := by
  intro eqn
  unfold NatDvd
  have mulRaw :
      NatMul (natToUnary p) (natToUnary q)
        (natMulFn (natToUnary p) (natToUnary q)) :=
    natMulFn_rel (natToUnary_unary p) (natToUnary_unary q)
  have sameProduct :
      hsame (natMulFn (natToUnary p) (natToUnary q)) (natToUnary n) := by
    rw [natMulFn_natToUnary_local]
    rw [eqn]
    rfl
  exact ⟨natToUnary q, natToUnary_unary q,
    (NatMul_result_hsame_transport mulRaw sameProduct).right⟩

theorem NatDvd_factor {p n : Nat} :
    NatDvd p n -> ∃ q : Nat, n = p * q := by
  intro divides
  unfold NatDvd at divides
  cases divides with
  | intro q qData =>
      exact ⟨bwordLength q, by
        calc
          n = bwordLength (natToUnary n) := (natToUnary_length n).symm
          _ = bwordLength (natToUnary p) * bwordLength q :=
            NatMul_bwordLength qData.right
          _ = p * bwordLength q :=
            congrArg (fun x => x * bwordLength q) (natToUnary_length p)⟩

theorem NatDvd_iff_factor (p n : Nat) :
    NatDvd p n ↔ ∃ q : Nat, n = p * q := by
  constructor
  · exact NatDvd_factor
  · intro h
    cases h with
    | intro q eqn =>
        exact NatDvd_of_factor eqn

theorem NatModEq_zero_of_NatDvd {p n : Nat} :
    NatDvd p n -> NatModEq p n 0 := by
  intro divides
  cases NatDvd_factor divides with
  | intro q eqn =>
      exact ⟨0, q, by
        rw [eqn]
        rw [Nat.mul_zero, Nat.add_zero, Nat.zero_add]⟩

theorem NatPrimeUp_Euclid {p a b : Nat} :
    NatPrimeUp p -> NatDvd p (a * b) -> NatDvd p a ∨ NatDvd p b := by
  intro prime dividesProduct
  unfold NatPrimeUp at prime
  unfold NatDvd at dividesProduct
  have productRaw :
      NatMul (natToUnary a) (natToUnary b)
        (natMulFn (natToUnary a) (natToUnary b)) :=
    natMulFn_rel (natToUnary_unary a) (natToUnary_unary b)
  have product :
      NatMul (natToUnary a) (natToUnary b) (natToUnary (a * b)) :=
    (NatMul_result_hsame_transport productRaw (by
      rw [natMulFn_natToUnary_local]
      rfl)).right
  exact
    NatEuclidPrime_product_left_or_right
      (NatPrime.toNatEuclidPrime prime)
      (natToUnary_unary a) (natToUnary_unary b) product dividesProduct

theorem lucas_rhs_eval_source (p m n : Nat) :
    digitEval p (baseDigits p m) = m ∧ digitEval p (baseDigits p n) = n := by
  exact ⟨digitEval_baseDigits p m, digitEval_baseDigits p n⟩

end BEDC.Derived.LucasTheoremBinomUp
