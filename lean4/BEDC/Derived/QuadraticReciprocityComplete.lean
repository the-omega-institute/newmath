import BEDC.Derived.LegendreDichotomyUp
import BEDC.Derived.QuadraticReciprocityUp

namespace BEDC.Derived.QuadraticReciprocityComplete

open BEDC.FKernel.Hist
open BEDC.Derived.LegendreDichotomyUp
open BEDC.Derived.LegendreUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.QuadraticReciprocityUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModUp

/-!
本文件只暴露已经可由 kernel 检查的互反律输入层。
无条件二次互反律还需要把 `LegendreClassifies` 接到 `QRSign`
以及 Gauss 负剩余计数、floor-sum 奇偶和 Eisenstein 网格恒等式的桥。
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

#check legendre_dichotomy_for_quadratic_reciprocity
#check legendre_symbol_nonzero_pm_one_for_quadratic_reciprocity
#check gauss_eisenstein_quadratic_reciprocity_formula

end BEDC.Derived.QuadraticReciprocityComplete
