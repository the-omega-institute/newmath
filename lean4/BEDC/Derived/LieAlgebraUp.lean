import BEDC.Derived.VecSpaceUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LieAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.VecSpaceUp

def LieAlgebraSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def LieAlgebraSingletonBracket (x y : BHist) : BHist :=
  append x y

theorem LieAlgebraSingletonAdjoint_additive_linearity {x y z yz left right : BHist} :
    LieAlgebraSingletonCarrier x -> LieAlgebraSingletonCarrier y ->
      LieAlgebraSingletonCarrier z -> Cont y z yz -> Cont x yz left ->
        Cont (LieAlgebraSingletonBracket x y) (LieAlgebraSingletonBracket x z) right ->
          hsame left right ∧ LieAlgebraSingletonCarrier left ∧
            LieAlgebraSingletonCarrier right ∧ UnaryHistory left ∧ UnaryHistory right := by
  intro carrierX carrierY carrierZ yzRow leftRow rightRow
  have yzEmpty : hsame yz BHist.Empty :=
    cont_respects_hsame carrierY carrierZ yzRow (cont_left_unit BHist.Empty)
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame carrierX yzEmpty leftRow (cont_left_unit BHist.Empty)
  have bracketXYEmpty : hsame (LieAlgebraSingletonBracket x y) BHist.Empty := by
    exact append_eq_empty_iff.mpr (And.intro carrierX carrierY)
  have bracketXZEmpty : hsame (LieAlgebraSingletonBracket x z) BHist.Empty := by
    exact append_eq_empty_iff.mpr (And.intro carrierX carrierZ)
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame bracketXYEmpty bracketXZEmpty rightRow (cont_left_unit BHist.Empty)
  have sameLeftRight : hsame left right :=
    hsame_trans leftEmpty (hsame_symm rightEmpty)
  have leftUnary : UnaryHistory left :=
    unary_transport unary_empty (hsame_symm leftEmpty)
  have rightUnary : UnaryHistory right :=
    unary_transport unary_empty (hsame_symm rightEmpty)
  exact And.intro sameLeftRight
    (And.intro leftEmpty (And.intro rightEmpty (And.intro leftUnary rightUnary)))

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

theorem LieAlgebraSingletonAdjoint_acting_endpoint_additive_linearity
    {x z y xz left xy zy right : BHist} :
    VecSpaceSingletonCarrier x -> VecSpaceSingletonCarrier z -> VecSpaceSingletonCarrier y ->
      Cont x z xz -> Cont xz y left -> Cont x y xy -> Cont z y zy ->
        Cont xy zy right -> VecSpaceSingletonClassifier left right := by
  intro carrierX carrierZ carrierY xzRow leftRow xyRow zyRow rightRow
  have xzEmpty : hsame xz BHist.Empty := by
    cases carrierX
    cases carrierZ
    cases xzRow
    rfl
  have leftEmpty : hsame left BHist.Empty := by
    cases xzEmpty
    cases carrierY
    cases leftRow
    rfl
  have xyEmpty : hsame xy BHist.Empty := by
    cases carrierX
    cases carrierY
    cases xyRow
    rfl
  have zyEmpty : hsame zy BHist.Empty := by
    cases carrierZ
    cases carrierY
    cases zyRow
    rfl
  have rightEmpty : hsame right BHist.Empty := by
    cases xyEmpty
    cases zyEmpty
    cases rightRow
    rfl
  exact And.intro leftEmpty
    (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))

end BEDC.Derived.LieAlgebraUp
