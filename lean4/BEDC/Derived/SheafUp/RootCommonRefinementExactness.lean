import BEDC.Derived.SheafUp.ExactnessExport

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SheafRootCommonRefinement_exactness_obligation
    {point common openA openB sectionA sectionB germA germB refinedCommon refinedGermA
      refinedGermB : BHist} :
    SheafDisplayedCommonRefinementSpan point common openA openB sectionA sectionB germA germB ->
      hsame common refinedCommon ->
        Cont refinedCommon sectionA refinedGermA ->
          Cont refinedCommon sectionB refinedGermB ->
            SemanticNameCert
                (fun endpoint : BHist =>
                  SheafBHistPointGermLedger point refinedCommon sectionA endpoint)
                (fun endpoint : BHist =>
                  SheafBHistPointGermLedger point refinedCommon sectionA endpoint)
                (fun endpoint : BHist =>
                  SheafBHistPointGermLedger point refinedCommon sectionA endpoint ∧
                    exists paired : BHist,
                      SheafBHistPointGermLedger point refinedCommon sectionB paired ∧
                        hsame endpoint paired)
                hsame ∧
              SheafBHistPointGermComparison point refinedCommon sectionA refinedGermA
                refinedCommon sectionB refinedGermB refinedCommon ∧
                hsame refinedGermA refinedGermB := by
  intro span sameCommon refinedA refinedB
  have refinedSpan :
      SheafDisplayedCommonRefinementSpan point refinedCommon openA openB sectionA sectionB
        refinedGermA refinedGermB :=
    (SheafDisplayedCommonRefinementSpan_base_change_composition
      span sameCommon refinedA refinedB).left
  have cert :
      SemanticNameCert
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point refinedCommon sectionA endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point refinedCommon sectionA endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point refinedCommon sectionA endpoint ∧
            exists paired : BHist,
              SheafBHistPointGermLedger point refinedCommon sectionB paired ∧
                hsame endpoint paired)
        hsame :=
    SheafCoverPresentation_exactness refinedSpan
  have pairedRows :=
    SheafDisplayedCommonRefinementSpan_paired_refinements refinedSpan
  have comparisonRows :
      SheafBHistPointGermComparison point refinedCommon sectionA refinedGermA
          refinedCommon sectionB refinedGermB refinedCommon ∧
        Cont refinedCommon sectionA refinedGermA ∧
          Cont refinedCommon sectionB refinedGermB :=
    SheafBHistPointGermLedger_common_open_comparison
      pairedRows.right.left pairedRows.right.right
      refinedSpan.right.right.right.right.right.right
  exact And.intro cert
    (And.intro comparisonRows.left refinedSpan.right.right.right.right.right.right)

end BEDC.Derived.SheafUp
