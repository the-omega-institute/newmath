import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

def ConvRadCoefficientRingInclusion (a a' : Nat -> BHist) (rho : BHist) : Prop :=
  UnaryHistory rho ∧ ∀ n : Nat, ComplexHistoryClassifier (a n) (a' n)

theorem ConvRadCoefficientRingInclusion_geomBound_transport {a a' : Nat -> BHist}
    {rho r K : BHist} :
    ConvRadCoefficientRingInclusion a a' rho -> GeomBound a r K -> GeomBound a' r K := by
  intro inclusion bound
  exact And.intro bound.left
    (And.intro bound.right.left
      (fun n : Nat => (inclusion.right n).right.left))

end BEDC.Derived.ConvergenceRadiusUp
