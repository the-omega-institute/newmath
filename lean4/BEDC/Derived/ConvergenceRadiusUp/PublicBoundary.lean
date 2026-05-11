import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ConvergenceRadiusCheckedRowReduct_public_export {a : Nat -> BHist} {z0 R : BHist} :
    ConvRadCheckedRowReduct a z0 R ->
      PowerSeriesCarrier a z0 ∧ ConvRad a R ∧ UnaryHistory R ∧
        ∃ K : BHist -> BHist, ∀ {r : BHist}, UnaryHistory r -> Cont r (K r) R ->
          PowerSeriesCarrier a z0 ∧ GeomBound a r (K r) ∧ UnaryHistory R := by
  intro checked
  exact ⟨checked.left.left, checked.left.right, checked.left.right.left, checked.right⟩

end BEDC.Derived.ConvergenceRadiusUp
