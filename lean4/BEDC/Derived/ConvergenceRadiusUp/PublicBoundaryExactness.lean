import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ConvRadCheckedRowReduct_public_boundary_exactness {a : Nat -> BHist} {z0 R : BHist} :
    ConvRadCheckedRowReduct a z0 R ->
      PowerSeriesCarrier a z0 ∧ ConvRad a R ∧ UnaryHistory R ∧
        (∃ K : BHist -> BHist, ∀ {r : BHist}, UnaryHistory r -> Cont r (K r) R ->
          PowerSeriesCarrier a z0 ∧ GeomBound a r (K r) ∧ UnaryHistory R) := by
  intro checked
  exact And.intro checked.left.left
    (And.intro checked.left.right
      (And.intro checked.left.right.left checked.right))

end BEDC.Derived.ConvergenceRadiusUp
