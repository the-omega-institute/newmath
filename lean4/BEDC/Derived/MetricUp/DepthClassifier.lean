import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist

theorem MetricDistanceDepth_zero_iff_empty {d : BHist} :
    MetricDistanceDepth d = 0 ↔ hsame d BHist.Empty := by
  constructor
  · intro depthZero
    cases d with
    | Empty =>
        exact hsame_refl BHist.Empty
    | e0 d =>
        cases depthZero
    | e1 d =>
        cases depthZero
  · intro sameEmpty
    cases sameEmpty
    rfl

end BEDC.Derived.MetricUp
