import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LieAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

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

end BEDC.Derived.LieAlgebraUp
