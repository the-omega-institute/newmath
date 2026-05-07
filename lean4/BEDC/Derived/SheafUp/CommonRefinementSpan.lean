import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafDisplayedCommonRefinementSpan
    (point common openA openB sectionA sectionB germA germB : BHist) : Prop :=
  UnaryHistory point ∧ UnaryHistory common ∧ hsame common openA ∧ hsame common openB ∧
    Cont common sectionA germA ∧ Cont common sectionB germB ∧ hsame germA germB

theorem SheafDisplayedCommonRefinementSpan_paired_refinements
    {point common openA openB sectionA sectionB germA germB : BHist} :
    SheafDisplayedCommonRefinementSpan point common openA openB sectionA sectionB germA
      germB ->
      SheafBHistPointGermComparison point openA sectionA germA openB sectionB germB common ∧
        SheafBHistPointGermLedger point common sectionA germA ∧
          SheafBHistPointGermLedger point common sectionB germB := by
  intro span
  have openAUnary : UnaryHistory openA :=
    unary_transport span.right.left span.right.right.left
  have openBUnary : UnaryHistory openB :=
    unary_transport span.right.left span.right.right.right.left
  exact And.intro
    (And.intro span.left
      (And.intro openAUnary
        (And.intro openBUnary
          (And.intro span.right.left
            (And.intro span.right.right.left
              (And.intro span.right.right.right.left
                (And.intro span.right.right.right.right.left
                  (And.intro span.right.right.right.right.right.left
                    span.right.right.right.right.right.right))))))))
    (And.intro
      (And.intro span.left
        (And.intro span.right.left span.right.right.right.right.left))
      (And.intro span.left
        (And.intro span.right.left span.right.right.right.right.right.left)))

theorem SheafDisplayedCommonRefinementSpan_base_change_composition
    {point common openA openB sectionA sectionB germA germB pulledCommon pulledGermA
      pulledGermB : BHist} :
    SheafDisplayedCommonRefinementSpan point common openA openB sectionA sectionB germA
      germB ->
      hsame common pulledCommon -> Cont pulledCommon sectionA pulledGermA ->
        Cont pulledCommon sectionB pulledGermB ->
          SheafDisplayedCommonRefinementSpan point pulledCommon openA openB sectionA sectionB
              pulledGermA pulledGermB ∧
            hsame germA pulledGermA ∧ hsame germB pulledGermB := by
  intro span sameCommon pulledA pulledB
  have pulledCommonUnary : UnaryHistory pulledCommon :=
    unary_transport span.right.left sameCommon
  have pulledOpenA : hsame pulledCommon openA :=
    hsame_trans (hsame_symm sameCommon) span.right.right.left
  have pulledOpenB : hsame pulledCommon openB :=
    hsame_trans (hsame_symm sameCommon) span.right.right.right.left
  have sameA : hsame germA pulledGermA :=
    cont_respects_hsame sameCommon (hsame_refl sectionA)
      span.right.right.right.right.left pulledA
  have sameB : hsame germB pulledGermB :=
    cont_respects_hsame sameCommon (hsame_refl sectionB)
      span.right.right.right.right.right.left pulledB
  have pulledSame : hsame pulledGermA pulledGermB :=
    hsame_trans (hsame_symm sameA)
      (hsame_trans span.right.right.right.right.right.right sameB)
  exact And.intro
    (And.intro span.left
      (And.intro pulledCommonUnary
        (And.intro pulledOpenA
          (And.intro pulledOpenB
            (And.intro pulledA
              (And.intro pulledB pulledSame))))))
    (And.intro sameA sameB)

theorem SheafDisplayedCommonRefinementSpan_symmetric
    {point common openA openB sectionA sectionB germA germB : BHist} :
    SheafDisplayedCommonRefinementSpan point common openA openB sectionA sectionB germA
      germB ->
      SheafDisplayedCommonRefinementSpan point common openB openA sectionB sectionA germB
        germA := by
  intro span
  exact And.intro span.left
    (And.intro span.right.left
      (And.intro span.right.right.right.left
        (And.intro span.right.right.left
          (And.intro span.right.right.right.right.right.left
            (And.intro span.right.right.right.right.left
              (hsame_symm span.right.right.right.right.right.right))))))

end BEDC.Derived.SheafUp
