import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.AbelianCatUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem AbelianCatKernelCokernel_visible_factorization
    {f kerObj cokObj imageObj coimageObj comparison recomposed : BHist} :
    hsame f BHist.Empty -> Cont BHist.Empty f kerObj -> Cont f BHist.Empty cokObj ->
      Cont kerObj cokObj imageObj -> Cont imageObj BHist.Empty coimageObj ->
        Cont coimageObj BHist.Empty comparison -> Cont comparison BHist.Empty recomposed ->
          hsame kerObj BHist.Empty ∧ hsame cokObj BHist.Empty ∧
            hsame imageObj BHist.Empty ∧ hsame coimageObj BHist.Empty ∧
              hsame comparison BHist.Empty ∧ hsame recomposed f ∧ UnaryHistory kerObj ∧
                UnaryHistory cokObj ∧ UnaryHistory imageObj ∧ UnaryHistory coimageObj ∧
                  UnaryHistory comparison ∧ UnaryHistory recomposed := by
  intro fEmpty kerReadback cokReadback imageReadback coimageReadback comparisonReadback
    recomposedReadback
  have sameKerF : hsame kerObj f :=
    cont_left_unit_result kerReadback
  have kerEmpty : hsame kerObj BHist.Empty :=
    hsame_trans sameKerF fEmpty
  have sameCokF : hsame cokObj f :=
    cont_right_unit_result cokReadback
  have cokEmpty : hsame cokObj BHist.Empty :=
    hsame_trans sameCokF fEmpty
  have imageEmpty : hsame imageObj BHist.Empty :=
    cont_respects_hsame kerEmpty cokEmpty imageReadback (cont_left_unit BHist.Empty)
  have sameCoimageImage : hsame coimageObj imageObj :=
    cont_right_unit_result coimageReadback
  have coimageEmpty : hsame coimageObj BHist.Empty :=
    hsame_trans sameCoimageImage imageEmpty
  have sameComparisonCoimage : hsame comparison coimageObj :=
    cont_right_unit_result comparisonReadback
  have comparisonEmpty : hsame comparison BHist.Empty :=
    hsame_trans sameComparisonCoimage coimageEmpty
  have sameRecomposedComparison : hsame recomposed comparison :=
    cont_right_unit_result recomposedReadback
  have recomposedEmpty : hsame recomposed BHist.Empty :=
    hsame_trans sameRecomposedComparison comparisonEmpty
  have recomposedF : hsame recomposed f :=
    hsame_trans recomposedEmpty (hsame_symm fEmpty)
  have kerUnary : UnaryHistory kerObj :=
    unary_transport unary_empty (hsame_symm kerEmpty)
  have cokUnary : UnaryHistory cokObj :=
    unary_transport unary_empty (hsame_symm cokEmpty)
  have imageUnary : UnaryHistory imageObj :=
    unary_transport unary_empty (hsame_symm imageEmpty)
  have coimageUnary : UnaryHistory coimageObj :=
    unary_transport unary_empty (hsame_symm coimageEmpty)
  have comparisonUnary : UnaryHistory comparison :=
    unary_transport unary_empty (hsame_symm comparisonEmpty)
  have recomposedUnary : UnaryHistory recomposed :=
    unary_transport unary_empty (hsame_symm recomposedEmpty)
  exact And.intro kerEmpty
    (And.intro cokEmpty
      (And.intro imageEmpty
        (And.intro coimageEmpty
          (And.intro comparisonEmpty
            (And.intro recomposedF
              (And.intro kerUnary
                (And.intro cokUnary
                  (And.intro imageUnary
                    (And.intro coimageUnary
                      (And.intro comparisonUnary recomposedUnary))))))))))

end BEDC.Derived.AbelianCatUp
