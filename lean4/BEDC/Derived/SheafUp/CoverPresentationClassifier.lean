import BEDC.Derived.SheafUp.ExactnessExport

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def SheafCoverPresentationClassifier
    (point common openA openB sectionA sectionB germA germB : BHist) : Prop :=
  SheafDisplayedCommonRefinementSpan point common openA openB sectionA sectionB germA
      germB ∧
    SemanticNameCert
      (fun endpoint : BHist => SheafBHistPointGermLedger point common sectionA endpoint)
      (fun endpoint : BHist => SheafBHistPointGermLedger point common sectionA endpoint)
      (fun endpoint : BHist =>
        SheafBHistPointGermLedger point common sectionA endpoint ∧
          exists paired : BHist,
            SheafBHistPointGermLedger point common sectionB paired ∧ hsame endpoint paired)
      hsame

theorem SheafCoverPresentationClassifier_exactness
    {point common openA openB sectionA sectionB germA germB : BHist} :
    SheafDisplayedCommonRefinementSpan point common openA openB sectionA sectionB germA
      germB ->
      SheafCoverPresentationClassifier point common openA openB sectionA sectionB germA
        germB := by
  intro span
  exact And.intro span (SheafCoverPresentation_exactness span)

end BEDC.Derived.SheafUp
