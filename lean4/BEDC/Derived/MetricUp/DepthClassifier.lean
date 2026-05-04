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

theorem MetricDistanceDepth_positive_iff_nonempty {d : BHist} :
    (0 < MetricDistanceDepth d) <-> (hsame d BHist.Empty -> False) := by
  constructor
  · intro positive sameEmpty
    cases d with
    | Empty =>
        cases positive
    | e0 d =>
        exact not_hsame_e0_empty sameEmpty
    | e1 d =>
        exact not_hsame_e1_empty sameEmpty
  · intro nonempty
    cases d with
    | Empty =>
        exact False.elim (nonempty (hsame_refl BHist.Empty))
    | e0 d =>
        exact Nat.succ_pos (MetricDistanceDepth d)
    | e1 d =>
        exact Nat.succ_pos (MetricDistanceDepth d)

end BEDC.Derived.MetricUp
