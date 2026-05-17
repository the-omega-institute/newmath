import BEDC.FKernel.Cont
import BEDC.FKernel.Mark

namespace BEDC.Derived.GroundRefutationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

def GroundRefutationCarrier (A F H C P N : BHist) : Prop :=
  Cont A F H ∧ Cont H C P ∧ hsame P N ∧ hsame A A ∧ hsame F F ∧
    hsame H H ∧ hsame C C ∧ hsame N N

theorem GroundRefutationNameCertObligations
    {A F H C P N bottom : BHist}
    (carrier : GroundRefutationCarrier A F H C P N)
    (route : Cont A F bottom) :
    Cont A F bottom ∧ hsame A A ∧ hsame F F ∧ hsame H H ∧ hsame C C ∧
      hsame P P ∧ hsame N N ∧ msame BMark.b0 BMark.b0 := by
  -- BEDC touchpoint anchor: BHist Cont hsame msame BMark
  exact
    ⟨route, carrier.right.right.right.left, carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left, rfl,
      carrier.right.right.right.right.right.right.right, rfl⟩

theorem GroundRefutationCarrier_ground_loop_boundary {A F H C P N : BHist}
    (carrier : GroundRefutationCarrier A F H C P N) :
    Cont A (append F C) P ∧ hsame P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame append
  constructor
  · cases carrier with
    | intro first rest =>
        cases rest with
        | intro second rest =>
            cases first
            cases second
            exact append_assoc A F C
  · exact carrier.right.right.left

end BEDC.Derived.GroundRefutationUp
