import BEDC.Derived.SheafUp.CommonRefinementSpan

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafRestrictedCommonRefinementLedger
    (point fixedOpen common openA openB sectionA sectionB germA germB restrictedA
      restrictedB : BHist) : Prop :=
  UnaryHistory fixedOpen ∧ hsame common fixedOpen ∧ hsame openA fixedOpen ∧
    hsame openB fixedOpen ∧
      SheafDisplayedCommonRefinementSpan point common openA openB sectionA sectionB germA
        germB ∧
        Cont fixedOpen sectionA restrictedA ∧ Cont fixedOpen sectionB restrictedB

theorem SheafRestrictedCommonRefinementLedger_forgetful_exactness
    {point fixedOpen common openA openB sectionA sectionB germA germB restrictedA
      restrictedB : BHist} :
    SheafRestrictedCommonRefinementLedger point fixedOpen common openA openB sectionA
      sectionB germA germB restrictedA restrictedB ->
      SheafDisplayedCommonRefinementSpan point common openA openB sectionA sectionB germA
          germB ∧
        UnaryHistory fixedOpen ∧ hsame common fixedOpen ∧
          SheafBHistPointGermComparison point openA sectionA germA openB sectionB germB
            common := by
  intro ledger
  have span :
      SheafDisplayedCommonRefinementSpan point common openA openB sectionA sectionB germA
        germB :=
    ledger.right.right.right.right.left
  have paired := SheafDisplayedCommonRefinementSpan_paired_refinements span
  exact And.intro span
    (And.intro ledger.left (And.intro ledger.right.left paired.left))

end BEDC.Derived.SheafUp
