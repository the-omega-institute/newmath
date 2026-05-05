import BEDC.Derived.ComplexTopologyUp

namespace BEDC.Derived.ComplexTopologyUp

open BEDC.FKernel.Hist

theorem ComplexTopologyOpenDiskGap_visible_radius_double_descent
    {center radiusTail point gap : BHist} :
    ComplexTopologyOpenDiskGap center (BHist.e1 (BHist.e1 radiusTail)) point gap ->
      (gap = BHist.Empty ∧ hsame point (BHist.e1 (BHist.e1 radiusTail))) ∨
        (∃ gapTail : BHist,
          gap = BHist.e1 gapTail ∧
            ((gapTail = BHist.Empty ∧ hsame point (BHist.e1 radiusTail)) ∨
              (∃ gapTailTail : BHist,
                gapTail = BHist.e1 gapTailTail ∧
                  ComplexTopologyOpenDiskGap center radiusTail point gapTailTail))) := by
  intro disk
  cases ComplexTopologyOpenDiskGap_visible_radius_gap_cases disk with
  | inl visible =>
      exact Or.inl visible
  | inr descended =>
      cases descended with
      | intro gapTail tailData =>
          cases tailData with
          | intro gapEq tailDisk =>
              cases ComplexTopologyOpenDiskGap_visible_radius_gap_cases tailDisk with
              | inl tailVisible =>
                  exact Or.inr
                    (Exists.intro gapTail (And.intro gapEq (Or.inl tailVisible)))
              | inr tailDescended =>
                  cases tailDescended with
                  | intro gapTailTail tailTailData =>
                      exact Or.inr
                        (Exists.intro gapTail
                          (And.intro gapEq
                            (Or.inr (Exists.intro gapTailTail tailTailData))))

end BEDC.Derived.ComplexTopologyUp
