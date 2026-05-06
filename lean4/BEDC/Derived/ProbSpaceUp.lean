import BEDC.FKernel.Unary
import BEDC.Derived.GroupUp
import BEDC.Derived.PreorderUp

namespace BEDC.Derived.ProbSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.PreorderUp

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

theorem ProbSpaceMonotoneEvent_bounds {event gap middle rest omega one : BHist} :
    UnaryHistory event -> UnaryHistory gap -> UnaryHistory rest -> Cont event gap middle ->
      Cont middle rest omega -> hsame omega one ->
        PreorderPrefixLE event middle ∧ PreorderPrefixLE middle one ∧
          PreorderPrefixLE event one ∧ UnaryHistory middle ∧ UnaryHistory omega := by
  intro eventUnary gapUnary restUnary eventMiddle middleOmega sameOmegaOne
  have middleUnary : UnaryHistory middle :=
    unary_cont_closed eventUnary gapUnary eventMiddle
  have omegaUnary : UnaryHistory omega :=
    unary_cont_closed middleUnary restUnary middleOmega
  have eventMiddleLE : PreorderPrefixLE event middle :=
    Exists.intro gap (And.intro gapUnary eventMiddle)
  have middleOmegaLE : PreorderPrefixLE middle omega :=
    Exists.intro rest (And.intro restUnary middleOmega)
  have omegaOneLE : PreorderPrefixLE omega one :=
    PreorderPrefixLE_of_hsame sameOmegaOne
  have middleOneLE : PreorderPrefixLE middle one :=
    PreorderPrefixLE_trans middleOmegaLE omegaOneLE
  have eventOneLE : PreorderPrefixLE event one :=
    PreorderPrefixLE_trans eventMiddleLE middleOneLE
  exact And.intro eventMiddleLE
    (And.intro middleOneLE
      (And.intro eventOneLE (And.intro middleUnary omegaUnary)))

end BEDC.Derived.ProbSpaceUp
