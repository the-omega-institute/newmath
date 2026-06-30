import BEDC.Derived.LegendreDichotomyUp
import BEDC.Derived.LegendreSymbolBridge
import BEDC.Derived.QuadraticReciprocityUp

namespace BEDC.Derived.QuadraticReciprocityComplete

open BEDC.FKernel.Hist
open BEDC.Derived.LegendreDichotomyUp
open BEDC.Derived.LegendreSymbolBridge
open BEDC.Derived.LegendreUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.QuadraticReciprocityUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModUp

/-!
本文件只暴露已经可由 kernel 检查的互反律输入层。
`LegendreSymbolBridge` 给出 Legendre 符号到 `QRSign` 输入的桥。
无条件二次互反律还需要 Gauss 负剩余计数、floor-sum 奇偶和 Eisenstein 网格恒等式的桥。
-/

theorem legendre_dichotomy_for_quadratic_reciprocity {p : BHist}
    (prime : NatPrime p) {a : ZMod p} :
    zmodNonzero a ->
      (IsQR prime a ∧ (LegendreNonresidue prime a -> False)) ∨
        (LegendreNonresidue prime a ∧ (IsQR prime a -> False)) := by
  intro aNonzero
  exact legendre_qr_nonresidue_dichotomy prime aNonzero

theorem legendre_symbol_nonzero_pm_one_for_quadratic_reciprocity {p : BHist}
    (prime : NatPrime p) {a : ZMod p} :
    zmodNonzero a ->
      ∃ s : BEDC.Algebra.Rel.IntegerUp,
        LegendreClassifies prime a s ∧
          (BEDC.Algebra.Rel.IntEq s legendreOne ∨
            BEDC.Algebra.Rel.IntEq s legendreNegOne) := by
  intro aNonzero
  exact legendre_symbol_nonzero_pm_one prime aNonzero

theorem gauss_eisenstein_quadratic_reciprocity_formula
    {p q : Nat} {pq qp : QRSign} :
    GaussLemmaShapeEq p q pq ->
      GaussLemmaShapeEq q p qp ->
        NegCountParityEqFloorSumEq p q ->
          NegCountParityEqFloorSumEq q p ->
            EisensteinFloorSumEq p q ->
              QRFormulaEq p q pq qp := by
  intro gaussPQ gaussQP parityPQ parityQP eisenstein
  exact quadraticReciprocityFormula_from_gauss_eisenstein
    gaussPQ gaussQP parityPQ parityQP eisenstein

theorem legendre_verified_inputs_quadratic_reciprocity_formula
    {pHist qHist : BHist} {p q : Nat} {pq qp : QRSign} :
    VerifiedQuadraticReciprocityInputs pHist qHist p q pq qp ->
      QRFormulaEq p q pq qp := by
  intro inputs
  exact quadratic_reciprocity_from_legendre_verified_inputs inputs

theorem legendre_verified_inputs_quadratic_reciprocity_package
    {pHist qHist : BHist} {p q : Nat} {pq qp : QRSign} :
    (inputs : VerifiedQuadraticReciprocityInputs pHist qHist p q pq qp) ->
      p = BEDC.FKernel.ExternalBinary.bwordLength pHist ∧
        q = BEDC.FKernel.ExternalBinary.bwordLength qHist ∧
        legendreQRSignInput inputs.pPrime
          (residueOfHistMod inputs.pPrime qHist inputs.qPrime.left) pq ∧
          legendreQRSignInput inputs.qPrime
            (residueOfHistMod inputs.qPrime pHist inputs.pPrime.left) qp ∧
            QRFormulaEq p q pq qp := by
  intro inputs
  exact quadratic_reciprocity_legendre_verified_package inputs

#check legendre_dichotomy_for_quadratic_reciprocity
#check legendre_symbol_nonzero_pm_one_for_quadratic_reciprocity
#check gauss_eisenstein_quadratic_reciprocity_formula
#check legendre_verified_inputs_quadratic_reciprocity_formula
#check legendre_verified_inputs_quadratic_reciprocity_package

end BEDC.Derived.QuadraticReciprocityComplete
