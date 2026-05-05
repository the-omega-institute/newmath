import BEDC.Derived.VecSpaceUp
import BEDC.FKernel.Cont

namespace BEDC.Derived.LieAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.VecSpaceUp

def LieAlgebraSingletonAdjointAction (x t : BHist) : BHist :=
  append x t

theorem LieAlgebraSingleton_adjoint_action_additive_linearity
    {x y z yz left xy xz right : BHist} :
    VecSpaceSingletonCarrier x -> VecSpaceSingletonCarrier y -> VecSpaceSingletonCarrier z ->
      Cont y z yz -> Cont x yz left -> Cont x y xy -> Cont x z xz ->
        Cont xy xz right -> VecSpaceSingletonClassifier left right := by
  intro carrierX carrierY carrierZ yzRow leftRow xyRow xzRow rightRow
  have yzEmpty : hsame yz BHist.Empty := by
    cases carrierY
    cases carrierZ
    cases yzRow
    rfl
  have leftEmpty : hsame left BHist.Empty := by
    cases carrierX
    cases yzEmpty
    cases leftRow
    rfl
  have xyEmpty : hsame xy BHist.Empty := by
    cases carrierX
    cases carrierY
    cases xyRow
    rfl
  have xzEmpty : hsame xz BHist.Empty := by
    cases carrierX
    cases carrierZ
    cases xzRow
    rfl
  have rightEmpty : hsame right BHist.Empty := by
    cases xyEmpty
    cases xzEmpty
    cases rightRow
    rfl
  exact And.intro leftEmpty
    (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))

end BEDC.Derived.LieAlgebraUp
