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

end BEDC.Derived.SheafUp
