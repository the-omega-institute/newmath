import BEDC.Derived.LegendreDichotomyUp
import BEDC.Derived.LegendreSymbolBridge
import BEDC.Derived.PhiDivisorSum
import BEDC.Derived.PrimitiveRootExistence
import BEDC.Derived.QuadraticReciprocityComplete

namespace BEDC.Derived.NumberTheoryCapstones

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Algebra.Rel (IntEq)
open BEDC.Derived.DivisorFunctionUp
open BEDC.Derived.LegendreDichotomyUp
open BEDC.Derived.LegendreSymbolBridge
open BEDC.Derived.LegendreUp
open BEDC.Derived.PhiDivisorSum
open BEDC.Derived.PrimeUp
open BEDC.Derived.PrimitiveRootExistence
open BEDC.Derived.PrimitiveRootUp
open BEDC.Derived.QuadraticReciprocityComplete
open BEDC.Derived.QuadraticReciprocityUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModResidueList (unaryPred)
open BEDC.Derived.ZModUp

/-!
数论收口入口只汇集已经由 kernel 检查的承重链。
无条件原根、无条件二次互反律、以及单位群循环性仍需要额外桥引理；
本文件不登记未闭合目标。
-/

theorem phi_divisor_sum_of_prime_factorization
    {n : BHist} {profile : BEDC.Derived.DivisorFunctionUp.PrimePowerProfile} :
    DivisorCountOfProfile n (divisorCountProfile profile) profile ->
      hsame (profilePhiDivisorSum profile) n := by
  intro profileData
  exact gauss_phi_divisor_sum_of_prime_factorization profileData

theorem order_layer_cardinality_bound {p k : BHist}
    (prime : NatPrime p) {xs : List (ZMod p)} :
    PrimeUnitOrderLayer prime k xs ->
      0 < bwordLength k ->
        xs.length <= bwordLength k := by
  intro layer kPositive
  exact primeUnitOrderLayer_bound prime layer kPositive

theorem top_order_layer_cardinality_bound {p : BHist}
    (prime : NatPrime p) {xs : List (ZMod p)} :
    PrimeUnitOrderLayer prime (unaryPred p) xs ->
      xs.length <= bwordLength p - 1 := by
  intro layer
  exact topOrderLayer_bound prime layer

theorem primitive_root_exists_from_search_certificate {p : BHist}
    (prime : NatPrime p) :
    PrimitiveRootSearchCertificate prime ->
      ∃ g : ZMod p,
        zmodNonzero g ∧
          IsPrimitiveRoot p prime.left (NatPrime_empty_absurd prime)
            (unaryPred p) g := by
  intro cert
  exact primitive_root_exists_of_search_certificate prime cert

theorem primitive_root_exists_from_top_order_layer {p : BHist}
    (prime : NatPrime p) {xs : List (ZMod p)} :
    PrimeUnitOrderLayer prime (unaryPred p) xs ->
      (∃ g : ZMod p, g ∈ xs) ->
        ∃ g : ZMod p,
          zmodNonzero g ∧
            IsPrimitiveRoot p prime.left (NatPrime_empty_absurd prime)
              (unaryPred p) g := by
  intro layer nonempty
  exact primitive_root_exists_of_top_order_layer prime layer nonempty

theorem primitive_root_order_divides_prime_minus_one {p phi : BHist}
    (prime : NatPrime p) {g : ZMod p} :
    zmodNonzero g ->
      IsPrimitiveRoot p prime.left (NatPrime_empty_absurd prime) phi g ->
        NatDivides phi (unaryPred p) := by
  intro gNonzero primitive
  exact
    BEDC.Derived.PrimitiveRootExistence.primitive_root_order_divides_prime_minus_one
      prime gNonzero primitive

theorem legendre_dichotomy_nonzero {p : BHist}
    (prime : NatPrime p) {a : ZMod p} :
    zmodNonzero a ->
      (IsQR prime a ∧ (LegendreNonresidue prime a -> False)) ∨
        (LegendreNonresidue prime a ∧ (IsQR prime a -> False)) := by
  intro aNonzero
  exact legendre_dichotomy_for_quadratic_reciprocity prime aNonzero

theorem legendre_symbol_nonzero_pm_one {p : BHist}
    (prime : NatPrime p) {a : ZMod p} :
    zmodNonzero a ->
      ∃ s : BEDC.Algebra.Rel.IntegerUp,
        LegendreClassifies prime a s ∧
          (BEDC.Algebra.Rel.IntEq s legendreOne ∨
            BEDC.Algebra.Rel.IntEq s legendreNegOne) := by
  intro aNonzero
  exact legendre_symbol_nonzero_pm_one_for_quadratic_reciprocity prime aNonzero

theorem legendre_symbol_search_bridge {p : BHist}
    (prime : NatPrime p) {a : ZMod p} (aNonzero : zmodNonzero a)
    (s : BEDC.Algebra.Rel.IntegerUp) :
    legendreSym prime a s ↔
      (legendreQRSearch prime a = true ∧ IntEq s legendreOne) ∨
        (legendreQRSearch prime a = false ∧ IntEq s legendreNegOne) := by
  exact legendreSym_nonzero_iff_dichotomySearch prime aNonzero s

theorem quadratic_reciprocity_from_gauss_eisenstein
    {p q : Nat} {pq qp : QRSign} :
    GaussLemmaShapeEq p q pq ->
      GaussLemmaShapeEq q p qp ->
        NegCountParityEqFloorSumEq p q ->
          NegCountParityEqFloorSumEq q p ->
            EisensteinFloorSumEq p q ->
              QRFormulaEq p q pq qp := by
  intro gaussPQ gaussQP parityPQ parityQP eisenstein
  exact gauss_eisenstein_quadratic_reciprocity_formula
    gaussPQ gaussQP parityPQ parityQP eisenstein

theorem quadratic_reciprocity_from_legendre_verified_inputs
    {pHist qHist : BHist} {p q : Nat} {pq qp : QRSign} :
    VerifiedQuadraticReciprocityInputs pHist qHist p q pq qp ->
      QRFormulaEq p q pq qp := by
  intro inputs
  exact legendre_verified_inputs_quadratic_reciprocity_formula inputs

theorem quadratic_reciprocity_verified_package
    {pHist qHist : BHist} {p q : Nat} {pq qp : QRSign} :
    (inputs : VerifiedQuadraticReciprocityInputs pHist qHist p q pq qp) ->
      p = bwordLength pHist ∧
        q = bwordLength qHist ∧
        legendreQRSignInput inputs.pPrime
          (residueOfHistMod inputs.pPrime qHist inputs.qPrime.left) pq ∧
          legendreQRSignInput inputs.qPrime
            (residueOfHistMod inputs.qPrime pHist inputs.pPrime.left) qp ∧
            QRFormulaEq p q pq qp := by
  intro inputs
  exact legendre_verified_inputs_quadratic_reciprocity_package inputs

#check phi_divisor_sum_of_prime_factorization
#check primitive_root_exists_from_search_certificate
#check primitive_root_exists_from_top_order_layer
#check quadratic_reciprocity_from_gauss_eisenstein
#check quadratic_reciprocity_from_legendre_verified_inputs
#check quadratic_reciprocity_verified_package

end BEDC.Derived.NumberTheoryCapstones
