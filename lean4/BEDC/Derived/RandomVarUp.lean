import BEDC.FKernel.Unary
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.RandomVarUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem RandomVarTotalPreimage_composition_exactness
    {sourceTotal middleTotal targetTotal middlePreimage compositePreimage : BHist} :
    UnaryHistory sourceTotal -> UnaryHistory middleTotal -> hsame targetTotal BHist.Empty ->
      hsame middleTotal BHist.Empty -> Cont middleTotal targetTotal middlePreimage ->
        Cont sourceTotal middlePreimage compositePreimage ->
          UnaryHistory compositePreimage ∧ hsame compositePreimage sourceTotal := by
  intro sourceUnary _middleUnary targetEmpty middleEmpty middleReadback compositeReadback
  have middleTargetEmpty : Cont middleTotal BHist.Empty middlePreimage :=
    cont_hsame_transport (hsame_refl middleTotal) targetEmpty (hsame_refl middlePreimage)
      middleReadback
  have middlePreimageSame : hsame middlePreimage middleTotal :=
    cont_right_unit_result middleTargetEmpty
  have middlePreimageEmpty : hsame middlePreimage BHist.Empty :=
    hsame_trans middlePreimageSame middleEmpty
  have compositeRightUnit : Cont sourceTotal BHist.Empty compositePreimage :=
    cont_hsame_transport (hsame_refl sourceTotal) middlePreimageEmpty
      (hsame_refl compositePreimage) compositeReadback
  have compositeSame : hsame compositePreimage sourceTotal :=
    cont_right_unit_result compositeRightUnit
  exact And.intro (unary_transport sourceUnary (hsame_symm compositeSame)) compositeSame

end BEDC.Derived.RandomVarUp
