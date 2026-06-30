import BEDC.Derived.LegendreDichotomyUp
import BEDC.Derived.QuadraticReciprocityUp

namespace BEDC.Derived.LegendreSymbolBridge

open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Algebra.Rel
open BEDC.Derived.LegendreDichotomyUp
open BEDC.Derived.LegendreUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.QuadraticReciprocityUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModUp

def legendreDichotomyCriterion {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (s : BEDC.Algebra.Rel.IntegerUp) : Prop :=
  (zmodEq a (zmodZero p prime.left (NatPrime_empty_absurd prime)) ∧
      IntEq s legendreZero) ∨
    (zmodNonzero a ∧ legendreQRSearch prime a = true ∧
      IntEq s legendreOne) ∨
      (zmodNonzero a ∧ legendreQRSearch prime a = false ∧
        IntEq s legendreNegOne)

theorem legendreSym_iff_dichotomyCriterion {p : BHist}
    (prime : NatPrime p) (a : ZMod p) (s : BEDC.Algebra.Rel.IntegerUp) :
    legendreSym prime a s ↔ legendreDichotomyCriterion prime a s := by
  constructor
  · intro symbol
    unfold legendreSym LegendreClassifies at symbol
    unfold legendreDichotomyCriterion
    cases symbol with
    | inl zeroBranch =>
        exact Or.inl zeroBranch
    | inr nonzeroBranch =>
        cases nonzeroBranch with
        | inl qrBranch =>
            exact Or.inr (Or.inl
              ⟨qrBranch.right.left,
                legendreQRSearch_complete prime qrBranch.right.left qrBranch.left,
                qrBranch.right.right⟩)
        | inr nonresidueBranch =>
            exact Or.inr (Or.inr
              ⟨nonresidueBranch.left.left,
                legendreQRSearch_false_of_nonresidue prime nonresidueBranch.left,
                nonresidueBranch.right⟩)
  · intro criterion
    unfold legendreSym LegendreClassifies
    unfold legendreDichotomyCriterion at criterion
    cases criterion with
    | inl zeroBranch =>
        exact Or.inl zeroBranch
    | inr nonzeroBranch =>
        cases nonzeroBranch with
        | inl qrBranch =>
            exact Or.inr (Or.inl
              ⟨legendreQRSearch_sound prime qrBranch.right.left,
                qrBranch.left, qrBranch.right.right⟩)
        | inr nonresidueBranch =>
            exact Or.inr (Or.inr
              ⟨legendreQRSearch_nonresidue_of_false prime
                  nonresidueBranch.left nonresidueBranch.right.left,
                nonresidueBranch.right.right⟩)

theorem legendreSym_nonzero_iff_dichotomySearch {p : BHist}
    (prime : NatPrime p) {a : ZMod p} (aNonzero : zmodNonzero a)
    (s : BEDC.Algebra.Rel.IntegerUp) :
    legendreSym prime a s ↔
      (legendreQRSearch prime a = true ∧ IntEq s legendreOne) ∨
        (legendreQRSearch prime a = false ∧ IntEq s legendreNegOne) := by
  constructor
  · intro symbol
    have criterion :
        legendreDichotomyCriterion prime a s :=
      (legendreSym_iff_dichotomyCriterion prime a s).mp symbol
    unfold legendreDichotomyCriterion at criterion
    cases criterion with
    | inl zeroBranch =>
        exact False.elim (aNonzero zeroBranch.left)
    | inr nonzeroBranch =>
        cases nonzeroBranch with
        | inl qrBranch =>
            exact Or.inl ⟨qrBranch.right.left, qrBranch.right.right⟩
        | inr nonresidueBranch =>
            exact Or.inr
              ⟨nonresidueBranch.right.left, nonresidueBranch.right.right⟩
  · intro searchBranch
    apply (legendreSym_iff_dichotomyCriterion prime a s).mpr
    unfold legendreDichotomyCriterion
    cases searchBranch with
    | inl qrBranch =>
        exact Or.inr (Or.inl
          ⟨aNonzero, qrBranch.left, qrBranch.right⟩)
    | inr nonresidueBranch =>
        exact Or.inr (Or.inr
          ⟨aNonzero, nonresidueBranch.left, nonresidueBranch.right⟩)

def qrSignMatchesLegendre (s : BEDC.Algebra.Rel.IntegerUp) (sign : QRSign) : Prop :=
  (sign = QRSign.pos ∧ IntEq s legendreOne) ∨
    (sign = QRSign.neg ∧ IntEq s legendreNegOne)

def legendreQRSignInput {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (sign : QRSign) : Prop :=
  zmodNonzero a ∧
    ∃ s : BEDC.Algebra.Rel.IntegerUp, legendreSym prime a s ∧
      qrSignMatchesLegendre s sign

theorem legendreQRSearch_true_sign_input {p : BHist}
    (prime : NatPrime p) {a : ZMod p} :
    zmodNonzero a -> legendreQRSearch prime a = true ->
      legendreQRSignInput prime a QRSign.pos := by
  intro aNonzero found
  exact ⟨aNonzero, legendreOne,
    (legendreSym_nonzero_iff_dichotomySearch prime aNonzero legendreOne).mpr
      (Or.inl ⟨found, BEDC.Derived.RationalUp.IntEq_refl _⟩),
    Or.inl ⟨rfl, BEDC.Derived.RationalUp.IntEq_refl _⟩⟩

theorem legendreQRSearch_false_sign_input {p : BHist}
    (prime : NatPrime p) {a : ZMod p} :
    zmodNonzero a -> legendreQRSearch prime a = false ->
      legendreQRSignInput prime a QRSign.neg := by
  intro aNonzero notFound
  exact ⟨aNonzero, legendreNegOne,
    (legendreSym_nonzero_iff_dichotomySearch prime aNonzero legendreNegOne).mpr
      (Or.inr ⟨notFound, BEDC.Derived.RationalUp.IntEq_refl _⟩),
    Or.inr ⟨rfl, BEDC.Derived.RationalUp.IntEq_refl _⟩⟩

def residueOfHistMod {p : BHist} (prime : NatPrime p)
    (a : BHist) (aUnary : UnaryHistory a) : ZMod p :=
  zmodFromNat p prime.left (NatPrime_empty_absurd prime) a aUnary

structure VerifiedQuadraticReciprocityInputs
    (pHist qHist : BHist) (p q : Nat) (pq qp : QRSign) where
  pPrime : NatPrime pHist
  qPrime : NatPrime qHist
  pLength : p = bwordLength pHist
  qLength : q = bwordLength qHist
  pqLegendre :
    legendreQRSignInput pPrime
      (residueOfHistMod pPrime qHist qPrime.left) pq
  qpLegendre :
    legendreQRSignInput qPrime
      (residueOfHistMod qPrime pHist pPrime.left) qp
  gaussPQ : GaussLemmaShapeEq p q pq
  gaussQP : GaussLemmaShapeEq q p qp
  parityPQ : NegCountParityEqFloorSumEq p q
  parityQP : NegCountParityEqFloorSumEq q p
  eisenstein : EisensteinFloorSumEq p q

theorem quadratic_reciprocity_from_legendre_verified_inputs
    {pHist qHist : BHist} {p q : Nat} {pq qp : QRSign} :
    VerifiedQuadraticReciprocityInputs pHist qHist p q pq qp ->
      QRFormulaEq p q pq qp := by
  intro inputs
  exact quadraticReciprocityFormula_from_gauss_eisenstein
    inputs.gaussPQ inputs.gaussQP inputs.parityPQ inputs.parityQP
    inputs.eisenstein

theorem quadratic_reciprocity_legendre_verified_package
    {pHist qHist : BHist} {p q : Nat} {pq qp : QRSign} :
    (inputs : VerifiedQuadraticReciprocityInputs pHist qHist p q pq qp) ->
      p = bwordLength pHist ∧ q = bwordLength qHist ∧
        legendreQRSignInput inputs.pPrime
          (residueOfHistMod inputs.pPrime qHist inputs.qPrime.left) pq ∧
          legendreQRSignInput inputs.qPrime
            (residueOfHistMod inputs.qPrime pHist inputs.pPrime.left) qp ∧
            QRFormulaEq p q pq qp := by
  intro inputs
  exact ⟨inputs.pLength, inputs.qLength, inputs.pqLegendre,
    inputs.qpLegendre,
    quadratic_reciprocity_from_legendre_verified_inputs inputs⟩

#check legendreSym_iff_dichotomyCriterion
#check legendreSym_nonzero_iff_dichotomySearch
#check legendreQRSearch_true_sign_input
#check legendreQRSearch_false_sign_input
#check quadratic_reciprocity_from_legendre_verified_inputs
#check quadratic_reciprocity_legendre_verified_package

end BEDC.Derived.LegendreSymbolBridge
