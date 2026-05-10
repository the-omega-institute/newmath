import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

theorem DiffFormDegreeProbeAligned_empty_iff {d : BHist} :
    DegreeProbeAligned d (ProbeBundle.Bnil : ProbeBundle BHist) ↔ hsame d BHist.Empty := by
  constructor
  · intro aligned
    cases aligned with
    | nil =>
        rfl
  · intro sameDegree
    cases sameDegree
    exact DegreeProbeAligned.nil

theorem DiffFormDegreeProbeAligned_hsame_arity_transport
    {d d' : BHist} {left right : ProbeBundle BHist} :
    DegreeProbeAligned d left -> DegreeProbeAligned d' right -> hsame d d' ->
      bundleLength left = bundleLength right := by
  intro leftAligned rightAligned sameDegree
  induction leftAligned generalizing d' right with
  | nil =>
      cases sameDegree
      cases rightAligned
      rfl
  | cons tailAligned ih =>
      cases sameDegree
      cases rightAligned with
      | cons rightTailAligned =>
          exact congrArg Nat.succ (ih rightTailAligned (hsame_refl _))

end BEDC.Derived.DiffFormUp
