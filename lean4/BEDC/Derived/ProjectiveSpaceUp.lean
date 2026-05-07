import BEDC.Derived.FieldUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.ProjectiveSpaceUp

open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def ProjectiveSpacePuncturedCarrier (scalar vector action : BHist) : Prop :=
  FieldSingletonNonZero scalar ∧ VecSpaceSingletonCarrier vector ∧ Cont scalar vector action

theorem ProjectiveSpacePuncturedCarrier_singleton_boundary {scalar vector action : BHist} :
    ProjectiveSpacePuncturedCarrier scalar vector action ->
      FieldSingletonCarrier scalar ∧ VecSpaceSingletonCarrier vector ∧
        VecSpaceSingletonCarrier action ∧ False := by
  intro carrier
  have scalarCarrier : FieldSingletonCarrier scalar := carrier.left.left
  have vectorCarrier : VecSpaceSingletonCarrier vector := carrier.right.left
  have actionCarrier : VecSpaceSingletonCarrier action :=
    cont_respects_hsame scalarCarrier vectorCarrier carrier.right.right
      (cont_right_unit BHist.Empty)
  have nonzeroAbsurd : False :=
    FieldSingletonNonZero_absurd carrier.left
  exact And.intro scalarCarrier
    (And.intro vectorCarrier
      (And.intro actionCarrier nonzeroAbsurd))

end BEDC.Derived.ProjectiveSpaceUp
