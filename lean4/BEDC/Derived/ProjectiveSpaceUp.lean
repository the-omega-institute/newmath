import BEDC.Derived.FieldUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.ProjectiveSpaceUp

open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Hist

def ProjectiveSpacePuncturedCarrier (h : BHist) : Prop :=
  VecSpaceSingletonCarrier h ∧ hsame h (BHist.e0 BHist.Empty)

theorem ProjectiveSpacePuncturedCarrier_empty_boundary {h : BHist} :
    ProjectiveSpacePuncturedCarrier h -> False := by
  intro carrier
  have nonzero : FieldSingletonNonZero h :=
    And.intro carrier.left carrier.right
  exact FieldSingletonNonZero_absurd nonzero

end BEDC.Derived.ProjectiveSpaceUp
