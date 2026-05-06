import BEDC.FKernel.Unary
import BEDC.Derived.GroupUp

namespace BEDC.Derived.ProbSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp

theorem ProbSpaceComplementMass_additive_readback {omega one event complement sum : BHist} :
    UnaryHistory event -> UnaryHistory complement -> Cont event complement sum ->
      hsame omega sum -> hsame omega one -> hsame sum one ∧ UnaryHistory sum := by
  intro eventCarrier complementCarrier sumRel sameOmegaSum sameOmegaOne
  exact And.intro (hsame_trans (hsame_symm sameOmegaSum) sameOmegaOne)
    (unary_cont_closed eventCarrier complementCarrier sumRel)

theorem ProbSpaceComplementMass_right_solution
    {omega one event complement sum inverseEvent target : BHist} :
    UnaryHistory event -> UnaryHistory complement -> Cont event complement sum ->
      hsame omega sum -> hsame omega one -> Cont one inverseEvent target ->
        Cont event target one -> hsame complement target ∧ UnaryHistory target := by
  intro eventCarrier complementCarrier sumRel sameOmegaSum sameOmegaOne
  intro _inverseRel targetRel
  have sumOne : hsame sum one :=
    hsame_trans (hsame_symm sameOmegaSum) sameOmegaOne
  have eventComplementOne : Cont event complement one :=
    cont_result_hsame_transport sumRel sumOne
  have sameComplementTarget : hsame complement target :=
    cont_left_cancel eventComplementOne targetRel
  exact And.intro sameComplementTarget
    (unary_transport complementCarrier sameComplementTarget)

theorem ProbSpaceComplementMass_one_minus_singleton {omega one event complement sum rhs : BHist} :
    GroupSingletonCarrier event -> GroupSingletonCarrier one -> UnaryHistory complement ->
      Cont event complement sum -> hsame omega sum -> hsame omega one ->
      Cont one (GroupSingletonInv event) rhs -> hsame complement rhs ∧ UnaryHistory rhs := by
  intro eventCarrier oneCarrier complementCarrier eventComplement sameOmegaSum sameOmegaOne oneMinus
  have sumOne : hsame sum one := hsame_trans (hsame_symm sameOmegaSum) sameOmegaOne
  have sumEmpty : hsame sum BHist.Empty := hsame_trans sumOne oneCarrier
  have eventComplementEmpty : append event complement = BHist.Empty :=
    Eq.trans eventComplement.symm sumEmpty
  have complementEmpty : hsame complement BHist.Empty :=
    (append_eq_empty_iff.mp eventComplementEmpty).right
  have rhsEmpty : hsame rhs BHist.Empty := hsame_trans oneMinus oneCarrier
  have sameComplementRhs : hsame complement rhs :=
    hsame_trans complementEmpty (hsame_symm rhsEmpty)
  exact And.intro sameComplementRhs (unary_transport complementCarrier sameComplementRhs)

end BEDC.Derived.ProbSpaceUp
