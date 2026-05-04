import BEDC.Derived.RealUp.Core

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp

theorem RealConstantHistoryClassifier_e1_e0_endpoint_absurd {tail d : BHist} :
    (RealConstantHistoryClassifier (BHist.e1 (BHist.e0 tail)) (BHist.e1 d) -> False) ∧
      (RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 (BHist.e0 tail)) ->
        False) := by
  constructor
  · intro classified
    have ratClassified : RatHistoryClassifier (BHist.e0 tail) d :=
      Iff.mp RealConstantHistoryClassifier_e1_iff_rat classified
    exact (RatHistoryClassifier_e0_endpoint_absurd (tail := tail) (d := d)).left
      ratClassified
  · intro classified
    have ratClassified : RatHistoryClassifier d (BHist.e0 tail) :=
      Iff.mp RealConstantHistoryClassifier_e1_iff_rat classified
    exact (RatHistoryClassifier_e0_endpoint_absurd (tail := tail) (d := d)).right
      ratClassified

end BEDC.Derived.RealUp
