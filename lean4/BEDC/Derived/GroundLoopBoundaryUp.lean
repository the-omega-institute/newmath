import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Assoc

namespace BEDC.Derived.GroundLoopBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont

def GroundLoopBoundaryCarrier (M S X R H C P N : BHist) : Prop :=
  msame BMark.b0 BMark.b0 ∧ msame BMark.b1 BMark.b1 ∧ Cont M S X ∧ Cont X R C ∧
    hsame P N ∧ hsame H H ∧ hsame N N

theorem GroundLoopBoundaryCarrier_ground_replay_composite
    {M S X R H C P N : BHist}
    (carrier : GroundLoopBoundaryCarrier M S X R H C P N) :
    Cont M (append S R) C ∧ hsame P N := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  constructor
  · cases carrier.right.right.left
    cases carrier.right.right.right.left
    exact append_assoc M S R
  · exact carrier.right.right.right.right.left

end BEDC.Derived.GroundLoopBoundaryUp
