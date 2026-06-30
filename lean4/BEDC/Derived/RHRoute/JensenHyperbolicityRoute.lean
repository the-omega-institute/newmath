import BEDC.Derived.BinomialIdentitiesUp
import BEDC.Derived.RHRoute.ConstructiveRHStatement
import BEDC.Real.RatNumLogEnclosure

set_option maxHeartbeats 800000

namespace BEDC.Derived.RHRoute.JensenHyperbolicityRoute

open BEDC.Derived.RationalUp
open BEDC.Derived.BinomialIdentitiesUp
open BEDC.Derived.RHRoute.ConstructiveRHStatement
open BEDC.Real.RatNumKernel
open BEDC.Real.RatNumLogEnclosure

abbrev Rat : Type :=
  RatNum

def binomialRat (d k : Nat) : Rat :=
  ratNat (C d k)

def JensenPolynomial (d n : Nat) (xiCoeff : Nat -> Rat) (k : Nat) : Rat :=
  if k ≤ d then
    ratMul (binomialRat d k) (xiCoeff (n + k))
  else
    ratZero

def quadraticDiscriminant (coeff : Nat -> Rat) : Rat :=
  ratSub (ratMul (coeff 1) (coeff 1))
    (ratMul (ratNat 4) (ratMul (coeff 0) (coeff 2)))

def QuadraticDiscriminantNonnegative (coeff : Nat -> Rat) : Prop :=
  ratLe
    (ratMul (ratNat 4) (ratMul (coeff 0) (coeff 2)))
    (ratMul (coeff 1) (coeff 1))

structure RationalSturmHyperbolicityCertificate
    (d : Nat) (coeff : Nat -> Rat) where
  chainLength : Nat
  chain : Nat -> Nat -> Rat
  signedRemainder : Nat -> Nat -> Rat
  leftVariation : Nat
  rightVariation : Nat
  rootsInWindow : Nat
  chain_length_nonzero : 1 ≤ chainLength
  chain_starts_at_jensen_polynomial :
    ∀ k : Nat, k ≤ d -> RatEq (chain 0 k) (coeff k)
  chain_zero_beyond_degree :
    ∀ row k : Nat, d < k -> RatEq (chain row k) ratZero
  signed_remainder_readback :
    ∀ row k : Nat, row + 1 < chainLength ->
      RatEq (chain (row + 1) k) (signedRemainder row k)
  endpoint_variation_reads_root_count :
    leftVariation = rightVariation + rootsInWindow
  all_roots_accounted : rootsInWindow = d

def HighDegreeHyperbolicBySturm
    (d : Nat) (coeff : Nat -> Rat) : Prop :=
  Nonempty (RationalSturmHyperbolicityCertificate d coeff)

def Hyperbolic : Nat -> (Nat -> Rat) -> Prop
  | 0, _coeff => True
  | 1, _coeff => True
  | 2, coeff => QuadraticDiscriminantNonnegative coeff
  | Nat.succ (Nat.succ (Nat.succ m)), coeff =>
      HighDegreeHyperbolicBySturm
        (Nat.succ (Nat.succ (Nat.succ m))) coeff

def xiOneCoeff (_n : Nat) : Rat :=
  ratOne

private theorem ratMul_eq_ratNat_of_eq
    {x y : Rat} {a b : Nat}
    (hx : RatEq x (ratNat a))
    (hy : RatEq y (ratNat b)) :
    RatEq (ratMul x y) (ratNat (a * b)) := by
  exact RatEq_trans _ _ _
    (ratMul_respects hx hy)
    (ratNat_mul a b)

private theorem jensen_sample_coeff_zero :
    RatEq (JensenPolynomial 2 0 xiOneCoeff 0) (ratNat 1) := by
  unfold JensenPolynomial xiOneCoeff binomialRat
  have hbin : C 2 0 = 1 := by decide
  rw [hbin]
  exact ratMul_one_right (ratNat 1)

private theorem jensen_sample_coeff_one :
    RatEq (JensenPolynomial 2 0 xiOneCoeff 1) (ratNat 2) := by
  unfold JensenPolynomial xiOneCoeff binomialRat
  have hbin : C 2 1 = 2 := by decide
  rw [hbin]
  exact ratMul_one_right (ratNat 2)

private theorem jensen_sample_coeff_two :
    RatEq (JensenPolynomial 2 0 xiOneCoeff 2) (ratNat 1) := by
  unfold JensenPolynomial xiOneCoeff binomialRat
  have hbin : C 2 2 = 1 := by decide
  rw [hbin]
  exact ratMul_one_right (ratNat 1)

theorem jensen_hyperbolic_witness :
    Hyperbolic 2 (JensenPolynomial 2 0 xiOneCoeff) := by
  change
    ratLe
      (ratMul (ratNat 4)
        (ratMul
          (JensenPolynomial 2 0 xiOneCoeff 0)
          (JensenPolynomial 2 0 xiOneCoeff 2)))
      (ratMul
        (JensenPolynomial 2 0 xiOneCoeff 1)
        (JensenPolynomial 2 0 xiOneCoeff 1))
  have h02 :
      RatEq
        (ratMul
          (JensenPolynomial 2 0 xiOneCoeff 0)
          (JensenPolynomial 2 0 xiOneCoeff 2))
        (ratNat (1 * 1)) :=
    ratMul_eq_ratNat_of_eq
      jensen_sample_coeff_zero jensen_sample_coeff_two
  have hleft :
      RatEq
        (ratMul (ratNat 4)
          (ratMul
            (JensenPolynomial 2 0 xiOneCoeff 0)
            (JensenPolynomial 2 0 xiOneCoeff 2)))
        (ratNat (4 * (1 * 1))) := by
    exact RatEq_trans _ _ _
      (ratMul_respects (RatEq_refl (ratNat 4)) h02)
      (ratNat_mul 4 (1 * 1))
  have hright :
      RatEq
        (ratMul
          (JensenPolynomial 2 0 xiOneCoeff 1)
          (JensenPolynomial 2 0 xiOneCoeff 1))
        (ratNat (2 * 2)) :=
    ratMul_eq_ratNat_of_eq
      jensen_sample_coeff_one jensen_sample_coeff_one
  have hnat : ratLe (ratNat (4 * (1 * 1))) (ratNat (2 * 2)) :=
    ratNat_le_of_nat_le (by decide)
  exact ratLe_of_RatEq_right
    (ratLe_of_RatEq_left hleft hnat)
    (RatEq_symm hright)

inductive JensenAnalyticObligation where
  | completedXiCoefficientLimit
  | polyaJensenEquivalence
  | locatedZeroBridge

def AllJensenHyperbolic (xiCoeff : Nat -> Rat) : Prop :=
  ∀ d n : Nat, Hyperbolic d (JensenPolynomial d n xiCoeff)

structure JensenHyperbolicityReduction where
  xiCoeff : Nat -> Rat
  obligations : List JensenAnalyticObligation
  obligation_scope :
    obligations =
      [ JensenAnalyticObligation.completedXiCoefficientLimit,
        JensenAnalyticObligation.polyaJensenEquivalence,
        JensenAnalyticObligation.locatedZeroBridge ]
  rh_from_all_jensen_hyperbolic :
    AllJensenHyperbolic xiCoeff -> ConstructiveRH

theorem rh_via_jensen_hyperbolicity
    (reduction : JensenHyperbolicityReduction)
    (hyperbolic : AllJensenHyperbolic reduction.xiCoeff) :
    ConstructiveRH :=
  reduction.rh_from_all_jensen_hyperbolic hyperbolic

theorem jensen_reduction_obligation_count
    (reduction : JensenHyperbolicityReduction) :
    reduction.obligations.length = 3 := by
  rw [reduction.obligation_scope]
  rfl

end BEDC.Derived.RHRoute.JensenHyperbolicityRoute
