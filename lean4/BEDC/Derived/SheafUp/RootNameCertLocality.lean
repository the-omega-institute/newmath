import BEDC.Derived.SheafUp.RootRestrictionRefinement

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SheafRootNameCertLocalityGluing_fields
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB ->
          hsame openHist restrictedOpen ->
            Cont restrictedOpen sectionA restrictedGermA ->
              Cont restrictedOpen sectionB restrictedGermB ->
                SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                    restrictedOpen sectionB restrictedGermB restrictedOpen ∧
                  hsame restrictedGermA restrictedGermB ∧
                    SemanticNameCert
                      (fun endpoint : BHist =>
                        SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
                      (fun endpoint : BHist =>
                        SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
                      (fun endpoint : BHist =>
                        SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
                      hsame := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    SheafBHistPointGermComparison_restricted_open_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have cert :
      SemanticNameCert
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point restrictedOpen sectionA endpoint)
        hsame :=
    SheafRestrictedOpenCarrier_semantic_name_certificate descent.left
  exact And.intro comparison (And.intro descent.right.right cert)

theorem SheafRootNameCertRefinementExactness_fields
    {point openA openB openC sectionHist germA germB germC route routeTarget : BHist} :
    SheafBHistPointGermLedger point openA sectionHist germA -> hsame openA openB ->
      Cont openB sectionHist germB -> hsame openB openC ->
        Cont openC sectionHist germC -> Cont openB route routeTarget ->
          hsame routeTarget openB ->
            SheafBHistPointGermLedger point openC sectionHist germC ∧
              hsame germA germC ∧ hsame route BHist.Empty ∧
                SemanticNameCert
                  (fun endpoint : BHist =>
                    SheafBHistPointGermLedger point openC sectionHist endpoint)
                  (fun endpoint : BHist =>
                    SheafBHistPointGermLedger point openC sectionHist endpoint)
                  (fun endpoint : BHist =>
                    SheafBHistPointGermLedger point openC sectionHist endpoint)
                  hsame := by
  intro ledger sameAB rowB sameBC rowC routeRow routeBoundary
  have fields :
      SheafBHistPointGermLedger point openC sectionHist germC ∧
        hsame germA germC ∧ hsame route BHist.Empty :=
    SheafRootRestrictionRefinement_obligation
      ledger sameAB rowB sameBC rowC routeRow routeBoundary
  have cert :
      SemanticNameCert
        (fun endpoint : BHist => SheafBHistPointGermLedger point openC sectionHist endpoint)
        (fun endpoint : BHist => SheafBHistPointGermLedger point openC sectionHist endpoint)
        (fun endpoint : BHist => SheafBHistPointGermLedger point openC sectionHist endpoint)
        hsame :=
    SheafRestrictedOpenCarrier_semantic_name_certificate fields.left
  exact And.intro fields.left
    (And.intro fields.right.left (And.intro fields.right.right cert))

end BEDC.Derived.SheafUp
