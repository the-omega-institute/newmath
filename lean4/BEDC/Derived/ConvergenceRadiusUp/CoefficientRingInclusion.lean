import BEDC.Derived.ConvergenceRadiusUp

namespace BEDC.Derived.ConvergenceRadiusUp

open BEDC.FKernel.Hist
open BEDC.Derived.ComplexUp

def ConvRadCoefficientRingInclusion (a b : Nat -> BHist) : Prop :=
  forall n : Nat, ComplexHistoryClassifier (a n) (b n)

theorem ConvRadCoefficientRingInclusion_pointwise_classifier {a b : Nat -> BHist} :
    ConvRadCoefficientRingInclusion a b ->
      forall n : Nat, ComplexHistoryClassifier (a n) (b n) := by
  intro inclusion n
  exact inclusion n

end BEDC.Derived.ConvergenceRadiusUp
