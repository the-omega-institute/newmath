import BEDC.Derived.AxisZeckendorf.Zeckendorf

namespace BEDC.Derived.ZeckendorfNormalUp

open BEDC.FKernel.Hist

theorem ZNormal_hsame_transport {h k : BHist} :
    BEDC.Derived.AxisZeckendorf.Zeckendorf.ZNormal h -> hsame h k ->
      BEDC.Derived.AxisZeckendorf.Zeckendorf.ZNormal k ∧
        (∀ t : BHist, k = BHist.e1 t ->
          (t = BHist.Empty ∨
            ∃ u : BHist, t = BHist.e0 u ∧
              BEDC.Derived.AxisZeckendorf.Zeckendorf.ZNormal (BHist.e0 u))) := by
  intro normal sameHK
  cases sameHK
  constructor
  · exact normal
  · intro t ht
    cases ht
    exact
      (BEDC.Derived.AxisZeckendorf.Zeckendorf.ZNormal_adjacent_one_inversion normal).left

end BEDC.Derived.ZeckendorfNormalUp
