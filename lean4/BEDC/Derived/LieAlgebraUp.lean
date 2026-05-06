import BEDC.Derived.VecSpaceUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LieAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.VecSpaceUp

def LieAlgebraAdjointAction (acting endpoint result : BHist) : Prop :=
  UnaryHistory acting ∧ UnaryHistory endpoint ∧ Cont acting endpoint result ∧ UnaryHistory result

theorem LieAlgebraAdjointAction_additive_linearity
    {acting y z yz left actionY actionZ rhs : BHist} :
    hsame acting BHist.Empty ->
      UnaryHistory y ->
        UnaryHistory z ->
          Cont y z yz ->
            LieAlgebraAdjointAction acting yz left ->
              LieAlgebraAdjointAction acting y actionY ->
                LieAlgebraAdjointAction acting z actionZ ->
                  Cont actionY actionZ rhs ->
                    hsame left rhs ∧ UnaryHistory left ∧ UnaryHistory rhs := by
  intro actingEmpty yUnary zUnary yzRow leftAction actionYAction actionZAction rhsRow
  have yzUnary : UnaryHistory yz := unary_cont_closed yUnary zUnary yzRow
  have leftRow : Cont acting yz left := leftAction.right.right.left
  have actionYRow : Cont acting y actionY := actionYAction.right.right.left
  have actionZRow : Cont acting z actionZ := actionZAction.right.right.left
  have sameLeftYZ : hsame left yz := by
    cases actingEmpty
    exact cont_left_unit_result leftRow
  have sameActionY : hsame actionY y := by
    cases actingEmpty
    exact cont_left_unit_result actionYRow
  have sameActionZ : hsame actionZ z := by
    cases actingEmpty
    exact cont_left_unit_result actionZRow
  have sameRhsYZ : hsame rhs yz :=
    cont_respects_hsame sameActionY sameActionZ rhsRow yzRow
  have rhsUnary : UnaryHistory rhs := unary_transport yzUnary (hsame_symm sameRhsYZ)
  exact And.intro (hsame_trans sameLeftYZ (hsame_symm sameRhsYZ))
    (And.intro leftAction.right.right.right rhsUnary)

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

theorem LieAlgebraSingletonAdjoint_scalar_endpoint_closure {r x y ry left xy right : BHist} :
    VecSpaceSingletonCarrier r -> VecSpaceSingletonCarrier x -> VecSpaceSingletonCarrier y ->
      Cont r y ry -> Cont x ry left -> Cont x y xy -> Cont r xy right ->
        VecSpaceSingletonClassifier left right ∧ VecSpaceSingletonCarrier left ∧
          VecSpaceSingletonCarrier right ∧ UnaryHistory left ∧ UnaryHistory right := by
  intro carrierR carrierX carrierY ryRow leftRow xyRow rightRow
  have ryEmpty : hsame ry BHist.Empty :=
    cont_respects_hsame carrierR carrierY ryRow (cont_left_unit BHist.Empty)
  have leftEmpty : hsame left BHist.Empty :=
    cont_respects_hsame carrierX ryEmpty leftRow (cont_left_unit BHist.Empty)
  have xyEmpty : hsame xy BHist.Empty :=
    cont_respects_hsame carrierX carrierY xyRow (cont_left_unit BHist.Empty)
  have rightEmpty : hsame right BHist.Empty :=
    cont_respects_hsame carrierR xyEmpty rightRow (cont_left_unit BHist.Empty)
  have leftRight : VecSpaceSingletonClassifier left right :=
    And.intro leftEmpty
      (And.intro rightEmpty (hsame_trans leftEmpty (hsame_symm rightEmpty)))
  have leftUnary : UnaryHistory left :=
    unary_transport unary_empty (hsame_symm leftEmpty)
  have rightUnary : UnaryHistory right :=
    unary_transport unary_empty (hsame_symm rightEmpty)
  exact And.intro leftRight
    (And.intro leftEmpty (And.intro rightEmpty (And.intro leftUnary rightUnary)))

end BEDC.Derived.LieAlgebraUp
