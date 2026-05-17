import BEDC.FKernel.Cont
import BEDC.FKernel.Mark

namespace BEDC.Derived.GroundRefutationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

def GroundRefutationCarrier (A F H C P N : BHist) : Prop :=
  hsame A A ∧ hsame F F ∧ hsame H H ∧ hsame C C ∧ hsame P P ∧
    hsame N N ∧ msame BMark.b0 BMark.b0

theorem GroundRefutationNameCertObligations
    {A F H C P N bottom : BHist}
    (carrier : GroundRefutationCarrier A F H C P N)
    (route : Cont A F bottom) :
    Cont A F bottom ∧ hsame A A ∧ hsame F F ∧ hsame H H ∧ hsame C C ∧
      hsame P P ∧ hsame N N ∧ msame BMark.b0 BMark.b0 := by
  -- BEDC touchpoint anchor: BHist Cont hsame msame BMark
  obtain ⟨sameA, sameF, sameH, sameC, sameP, sameN, markSame⟩ := carrier
  exact ⟨route, sameA, sameF, sameH, sameC, sameP, sameN, markSame⟩

end BEDC.Derived.GroundRefutationUp
