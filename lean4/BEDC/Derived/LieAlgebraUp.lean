import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LieAlgebraUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

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

end BEDC.Derived.LieAlgebraUp
