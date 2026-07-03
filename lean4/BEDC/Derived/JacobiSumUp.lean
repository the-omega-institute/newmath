import BEDC.Derived.DirichletCharacterUp
import BEDC.Derived.GaussSumUp
import BEDC.Derived.GaussianPrimeUp
import BEDC.Derived.SumTwoSquaresUp

namespace BEDC.Derived.JacobiSumUp

open BEDC.Algebra.FiniteFold
open BEDC.Algebra.Rel
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.DirichletCharacterUp
open BEDC.Derived.GaussSumUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModResidueList
open BEDC.Derived.ZModUp

abbrev IntegerUp : Type :=
  BEDC.Algebra.Rel.IntegerUp

abbrev IntEq : IntegerUp -> IntegerUp -> Prop :=
  BEDC.Algebra.Rel.IntEq

abbrev IntMul : IntegerUp -> IntegerUp -> IntegerUp :=
  BEDC.Algebra.Rel.IntMul

abbrev intZero : IntegerUp :=
  BEDC.Algebra.Rel.intZero

abbrev intOne : IntegerUp :=
  BEDC.Algebra.Rel.intOne

private abbrev intRing : RelCommRing IntegerUp IntEq :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing

variable {A : Type u} {r : A -> A -> Prop}

private theorem relMul_four_cross (R : RelCommRing A r)
    (a b c d : A) :
    r (R.mul (R.mul a b) (R.mul c d))
      (R.mul (R.mul a c) (R.mul b d)) := by
  have regroupLeft :
      r (R.mul (R.mul a b) (R.mul c d))
        (R.mul a (R.mul b (R.mul c d))) :=
    R.mul_assoc a b (R.mul c d)
  have commuteMiddle :
      r (R.mul b (R.mul c d)) (R.mul c (R.mul b d)) := by
    exact R.trans (R.symm (R.mul_assoc b c d))
      (R.trans
        (R.mul_congr (R.mul_comm b c) (R.refl d))
        (R.mul_assoc c b d))
  have moveMiddle :
      r (R.mul a (R.mul b (R.mul c d)))
        (R.mul a (R.mul c (R.mul b d))) :=
    R.mul_congr (R.refl a) commuteMiddle
  have regroupRight :
      r (R.mul a (R.mul c (R.mul b d)))
        (R.mul (R.mul a c) (R.mul b d)) :=
    R.symm (R.mul_assoc a c (R.mul b d))
  exact R.trans regroupLeft (R.trans moveMiddle regroupRight)

def zmodOneMinus {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) (a : ZMod n) : ZMod n :=
  zmodAdd n nUnary nNonempty
    (zmodOne n nUnary nNonempty)
    (zmodNeg n nUnary nNonempty a)

theorem zmodOneMinus_congr {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) {a b : ZMod n} :
    zmodEq a b ->
      zmodEq (zmodOneMinus nUnary nNonempty a)
        (zmodOneMinus nUnary nNonempty b) := by
  intro same
  exact zmodAdd_congr nUnary nNonempty
    (zmodEq_refl (zmodOne n nUnary nNonempty))
    (zmodNeg_congr nUnary nNonempty same)

def primeResidues {p : BHist} (prime : NatPrime p) : List (ZMod p) :=
  zmodZero p prime.left (NatPrime_empty_absurd prime) :: nonzeroResidues prime

theorem primeResidues_zero_mem {p : BHist} (prime : NatPrime p) :
    zmodZero p prime.left (NatPrime_empty_absurd prime) ∈ primeResidues prime := by
  exact List.Mem.head (nonzeroResidues prime)

theorem primeResidues_nonzero_tail_mem {p : BHist} (prime : NatPrime p)
    {x : ZMod p} :
    x ∈ nonzeroResidues prime -> x ∈ primeResidues prime := by
  intro mem
  exact List.Mem.tail (zmodZero p prime.left (NatPrime_empty_absurd prime)) mem

def jacobiTerm {p : BHist} (prime : NatPrime p)
    (chi psi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime))
    (a : ZMod p) : IntegerUp :=
  IntMul (chi.value a)
    (psi.value (zmodOneMinus prime.left (NatPrime_empty_absurd prime) a))

def jacobiSum {p : BHist} (prime : NatPrime p)
    (chi psi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) :
    IntegerUp :=
  listSum intRing (List.map (jacobiTerm prime chi psi) (primeResidues prime))

theorem jacobiSum_is_prime_residue_list_sum {p : BHist}
    (prime : NatPrime p)
    (chi psi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) :
    IntEq (jacobiSum prime chi psi)
      (listSum intRing
        (List.map (jacobiTerm prime chi psi) (primeResidues prime))) :=
  intRing.refl _

theorem jacobiTerm_respects {p : BHist} (prime : NatPrime p)
    (chi psi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime))
    {a b : ZMod p} :
    zmodEq a b -> IntEq (jacobiTerm prime chi psi a)
      (jacobiTerm prime chi psi b) := by
  intro same
  exact intRing.mul_congr (chi.respects same)
    (psi.respects
      (zmodOneMinus_congr prime.left
        (NatPrime_empty_absurd prime) same))

def characterProduct {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (chi psi : DirichletCharacter n nUnary nNonempty) :
    DirichletCharacter n nUnary nNonempty where
  value x := IntMul (chi.value x) (psi.value x)
  respects := by
    intro x y same
    exact intRing.mul_congr (chi.respects same) (psi.respects same)
  completely_multiplicative := by
    intro x y
    have chiMul := chi.completely_multiplicative x y
    have psiMul := psi.completely_multiplicative x y
    exact intRing.trans (intRing.mul_congr chiMul psiMul)
      (relMul_four_cross intRing
        (chi.value x) (chi.value y) (psi.value x) (psi.value y))
  zero_on_nonunits := by
    intro x xNonunit
    exact intRing.trans
      (intRing.mul_congr (chi.zero_on_nonunits x xNonunit)
        (intRing.refl (psi.value x)))
      (intRing.zero_mul (psi.value x))

theorem characterProduct_value {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (chi psi : DirichletCharacter n nUnary nNonempty)
    (x : ZMod n) :
    IntEq ((characterProduct nUnary nNonempty chi psi).value x)
      (IntMul (chi.value x) (psi.value x)) :=
  intRing.refl _

def CharacterNonprincipalWitness {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (chi : DirichletCharacter n nUnary nNonempty) : Prop :=
  ∃ x : ZMod n,
    zmodUnit n nUnary nNonempty x ∧
      (IntEq (chi.value x) intOne -> False)

def RelNonzero (R : RelCommRing A r) (x : A) : Prop :=
  r x R.zero -> False

def dirichletGaussSum {p : BHist} (prime : NatPrime p)
    (R : RelCommRing A r) (scale : IntegerUp -> A)
    (phase : CyclicPhase p A) (a : ZMod p)
    (chi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) : A :=
  gaussSum prime R scale phase a chi.value

theorem dirichletGaussSum_is_gaussSum {p : BHist}
    (prime : NatPrime p) (R : RelCommRing A r)
    (scale : IntegerUp -> A) (phase : CyclicPhase p A)
    (a : ZMod p)
    (chi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) :
    r (dirichletGaussSum prime R scale phase a chi)
      (gaussSum prime R scale phase a chi.value) :=
  R.refl _

def JacobiGaussRatioCrossRelation {p : BHist}
    (prime : NatPrime p) (R : RelCommRing A r)
    (scale : IntegerUp -> A) (phase : CyclicPhase p A)
    (a : ZMod p)
    (chi psi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) : Prop :=
  let chip := characterProduct prime.left (NatPrime_empty_absurd prime) chi psi
  r
    (R.mul (scale (jacobiSum prime chi psi))
      (dirichletGaussSum prime R scale phase a chip))
    (R.mul (dirichletGaussSum prime R scale phase a chi)
      (dirichletGaussSum prime R scale phase a psi))

structure JacobiGaussRelationCertificate {p : BHist}
    (prime : NatPrime p) (R : RelCommRing A r)
    (scale : IntegerUp -> A) (phase : CyclicPhase p A)
    (a : ZMod p)
    (chi psi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) where
  product_nonprincipal :
    CharacterNonprincipalWitness prime.left (NatPrime_empty_absurd prime)
      (characterProduct prime.left (NatPrime_empty_absurd prime) chi psi)
  product_gauss_nonzero :
    RelNonzero R
      (dirichletGaussSum prime R scale phase a
        (characterProduct prime.left (NatPrime_empty_absurd prime) chi psi))
  cross_relation :
    JacobiGaussRatioCrossRelation prime R scale phase a chi psi

theorem jacobiSum_gauss_ratio_cross_relation_from_certificate {p : BHist}
    (prime : NatPrime p) (R : RelCommRing A r)
    (scale : IntegerUp -> A) (phase : CyclicPhase p A)
    (a : ZMod p)
    (chi psi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) :
    JacobiGaussRelationCertificate prime R scale phase a chi psi ->
      JacobiGaussRatioCrossRelation prime R scale phase a chi psi := by
  intro cert
  exact cert.cross_relation

structure JacobiSqrtPrimeMagnitudeCertificate {p : BHist}
    (prime : NatPrime p) (R : RelCommRing A r)
    (scale : IntegerUp -> A) (absValue : A -> A) (sqrtPrime : A)
    (chi psi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) where
  chi_nonprincipal :
    CharacterNonprincipalWitness prime.left (NatPrime_empty_absurd prime) chi
  psi_nonprincipal :
    CharacterNonprincipalWitness prime.left (NatPrime_empty_absurd prime) psi
  product_nonprincipal :
    CharacterNonprincipalWitness prime.left (NatPrime_empty_absurd prime)
      (characterProduct prime.left (NatPrime_empty_absurd prime) chi psi)
  magnitude_relation :
    r (absValue (scale (jacobiSum prime chi psi))) sqrtPrime

theorem jacobiSqrtPrimeMagnitude_from_certificate {p : BHist}
    (prime : NatPrime p) (R : RelCommRing A r)
    (scale : IntegerUp -> A) (absValue : A -> A) (sqrtPrime : A)
    (chi psi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) :
    JacobiSqrtPrimeMagnitudeCertificate prime R scale absValue sqrtPrime chi psi ->
      r (absValue (scale (jacobiSum prime chi psi))) sqrtPrime := by
  intro cert
  exact cert.magnitude_relation

def primeInteger {p : BHist} (prime : NatPrime p) : IntegerUp :=
  BEDC.Derived.RationalUp.intOfNat p prime.left

structure SquareSumJacobiContact {p : BHist} (prime : NatPrime p)
    (R : RelCommRing A r) (scale : IntegerUp -> A)
    (absValue : A -> A) (sqrtPrime : A)
    (chi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) where
  prime_as_two_square :
    BEDC.Derived.SumTwoSquaresUp.IsSumTwoSquares (primeInteger prime)
  partner :
    DirichletCharacter p prime.left (NatPrime_empty_absurd prime)
  magnitude_certificate :
    JacobiSqrtPrimeMagnitudeCertificate prime R scale absValue sqrtPrime chi partner

theorem squareSumJacobiContact_exports_two_square {p : BHist}
    (prime : NatPrime p) (R : RelCommRing A r)
    (scale : IntegerUp -> A) (absValue : A -> A) (sqrtPrime : A)
    (chi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) :
    SquareSumJacobiContact prime R scale absValue sqrtPrime chi ->
      BEDC.Derived.SumTwoSquaresUp.IsSumTwoSquares (primeInteger prime) := by
  intro contact
  exact contact.prime_as_two_square

theorem squareSumJacobiContact_exports_gaussian_split {p : BHist}
    (prime : NatPrime p) (R : RelCommRing A r)
    (scale : IntegerUp -> A) (absValue : A -> A) (sqrtPrime : A)
    (chi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) :
    SquareSumJacobiContact prime R scale absValue sqrtPrime chi ->
      BEDC.Derived.GaussianPrimeUp.GaussianSplit (primeInteger prime) := by
  intro contact
  exact BEDC.Derived.GaussianPrimeUp.sum_two_squares_splits
    (squareSumJacobiContact_exports_two_square prime R scale absValue sqrtPrime chi contact)

theorem squareSumJacobiContact_exports_gaussian_split_and_prime {p : BHist}
    (prime : NatPrime p) (R : RelCommRing A r)
    (scale : IntegerUp -> A) (absValue : A -> A) (sqrtPrime : A)
    (chi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime))
    (z : BEDC.Derived.GaussianPrimeUp.GaussInt) :
    SquareSumJacobiContact prime R scale absValue sqrtPrime chi ->
      BEDC.Derived.GaussianPrimeUp.IntegerMultiplicativePrime
        (BEDC.Derived.GaussianPrimeUp.gaussNorm z) ->
        BEDC.Derived.GaussianPrimeUp.NormUnitReflectsGaussianUnit ->
          BEDC.Derived.GaussianPrimeUp.GaussianSplit (primeInteger prime) ∧
            BEDC.Derived.GaussianPrimeUp.GaussianPrime z := by
  intro contact normPrime unitReflect
  constructor
  · exact squareSumJacobiContact_exports_gaussian_split
      prime R scale absValue sqrtPrime chi contact
  · exact BEDC.Derived.GaussianPrimeUp.int_norm_prime_implies_gaussian_prime
      normPrime unitReflect

theorem squareSumJacobiContact_exports_split_with_ramified_two {p : BHist}
    (prime : NatPrime p) (R : RelCommRing A r)
    (scale : IntegerUp -> A) (absValue : A -> A) (sqrtPrime : A)
    (chi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) :
    SquareSumJacobiContact prime R scale absValue sqrtPrime chi ->
      BEDC.Derived.GaussianPrimeUp.GaussianSplit (primeInteger prime) ∧
        BEDC.Derived.GaussianPrimeUp.GaussEq
          (BEDC.Derived.GaussianPrimeUp.gaussMul
            BEDC.Derived.GaussianPrimeUp.gaussianOnePlusI
            BEDC.Derived.GaussianPrimeUp.gaussianOneMinusI)
          (BEDC.Derived.GaussianPrimeUp.gaussOfInt
            BEDC.Derived.GaussianPrimeUp.intTwo) := by
  intro contact
  constructor
  · exact squareSumJacobiContact_exports_gaussian_split
      prime R scale absValue sqrtPrime chi contact
  · exact BEDC.Derived.GaussianPrimeUp.gaussian_two_ramifies

theorem JacobiSumUp_definition_and_gauss_relation_surface {p : BHist}
    (prime : NatPrime p) (R : RelCommRing A r)
    (scale : IntegerUp -> A) (phase : CyclicPhase p A)
    (a : ZMod p)
    (chi psi :
      DirichletCharacter p prime.left (NatPrime_empty_absurd prime)) :
    IntEq (jacobiSum prime chi psi)
      (listSum intRing
        (List.map (jacobiTerm prime chi psi) (primeResidues prime))) ∧
      (JacobiGaussRelationCertificate prime R scale phase a chi psi ->
        JacobiGaussRatioCrossRelation prime R scale phase a chi psi) := by
  constructor
  · exact jacobiSum_is_prime_residue_list_sum prime chi psi
  · intro cert
    exact jacobiSum_gauss_ratio_cross_relation_from_certificate
      prime R scale phase a chi psi cert

end BEDC.Derived.JacobiSumUp
