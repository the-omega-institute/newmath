import BEDC.Derived.SheafUp.RootRestrictionRefinement
import BEDC.Derived.SheafUp.LocalityGluingCertificate
import BEDC.Derived.SheafUp.RootUnblock
import BEDC.Derived.SheafUp.CommonRefinementSpan

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

theorem SheafRootCoverLocalityGluing_obligation_surface
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              Cont restrictedOpen sectionA globalA ->
                Cont restrictedOpen sectionB globalB ->
                  SheafBHistPointGermComparison point restrictedOpen sectionA globalA
                      restrictedOpen sectionB globalB restrictedOpen ∧
                    SheafRootFaceRead restrictedOpen globalA .localityGluingRefinement ∧
                      hsame globalA globalB ∧
                        SemanticNameCert
                          (fun endpoint : BHist =>
                            SheafBHistPointGermComparison point restrictedOpen sectionA endpoint
                              restrictedOpen sectionB globalB restrictedOpen)
                          (fun endpoint : BHist =>
                            SheafBHistPointGermComparison point restrictedOpen sectionA endpoint
                              restrictedOpen sectionB globalB restrictedOpen)
                          (fun endpoint : BHist =>
                            SheafBHistPointGermComparison point restrictedOpen sectionA endpoint
                              restrictedOpen sectionB globalB restrictedOpen)
                          hsame := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB globalACont globalBCont
  have faces :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          SheafBHistPointGermComparison point restrictedOpen sectionA globalA
            restrictedOpen sectionB globalB restrictedOpen ∧
            SheafRootFaceRead restrictedOpen globalA .localityGluingRefinement ∧
              hsame globalA globalB :=
    SheafRootUnblock_locality_gluing_faces
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB globalACont globalBCont
  have cert :
      SemanticNameCert
        (fun endpoint : BHist =>
          SheafBHistPointGermComparison point restrictedOpen sectionA endpoint
            restrictedOpen sectionB globalB restrictedOpen)
        (fun endpoint : BHist =>
          SheafBHistPointGermComparison point restrictedOpen sectionA endpoint
            restrictedOpen sectionB globalB restrictedOpen)
        (fun endpoint : BHist =>
          SheafBHistPointGermComparison point restrictedOpen sectionA endpoint
            restrictedOpen sectionB globalB restrictedOpen)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro globalA faces.right.right.left
      · intro endpoint _carrier
        exact hsame_refl endpoint
      · intro endpoint endpoint' same
        exact hsame_symm same
      · intro endpoint endpoint' endpoint'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro endpoint endpoint' same carrier
        have transportedA : Cont restrictedOpen sectionA endpoint' :=
          cont_result_hsame_transport
            carrier.right.right.right.right.right.right.left same
        have transportedEndpoint : hsame endpoint' globalB :=
          hsame_trans (hsame_symm same)
            carrier.right.right.right.right.right.right.right.right
        exact And.intro carrier.left
          (And.intro carrier.right.left
            (And.intro carrier.right.right.left
              (And.intro carrier.right.right.right.left
                (And.intro carrier.right.right.right.right.left
                  (And.intro carrier.right.right.right.right.right.left
                    (And.intro transportedA
                      (And.intro carrier.right.right.right.right.right.right.right.left
                        transportedEndpoint)))))))
    · intro _endpoint source
      exact source
    · intro _endpoint source
      exact source
  exact And.intro faces.right.right.left
    (And.intro faces.right.right.right.left
      (And.intro faces.right.right.right.right cert))

theorem SheafRootCommonRefinement_obligation_carrier_exactness
    {point common openA openB sectionA sectionB germA germB globalA globalB exportedA
      exportedB : BHist} :
    SheafDisplayedCommonRefinementSpan point common openA openB sectionA sectionB germA
        germB ->
      Cont common sectionA globalA -> Cont common sectionB globalB -> hsame globalA exportedA ->
        hsame globalB exportedB ->
          SheafBHistPointGermLedger point common sectionA exportedA ∧
            SheafBHistPointGermLedger point common sectionB exportedB ∧
              hsame exportedA exportedB := by
  intro span globalACont globalBCont sameExportedA sameExportedB
  have rows :
      SheafBHistPointGermLedger point common sectionA globalA ∧
        SheafBHistPointGermLedger point common sectionB globalB ∧
          SheafBHistPointGermComparison point openA sectionA globalA openB sectionB globalB
              common ∧
            hsame globalA globalB :=
    SheafCommonRefinementGluing_carrier_invariance span globalACont globalBCont
  have exportedACont : Cont common sectionA exportedA :=
    cont_result_hsame_transport globalACont sameExportedA
  have exportedBCont : Cont common sectionB exportedB :=
    cont_result_hsame_transport globalBCont sameExportedB
  have ledgerA : SheafBHistPointGermLedger point common sectionA exportedA :=
    And.intro span.left (And.intro span.right.left exportedACont)
  have ledgerB : SheafBHistPointGermLedger point common sectionB exportedB :=
    And.intro span.left (And.intro span.right.left exportedBCont)
  have sameExported : hsame exportedA exportedB :=
    hsame_trans (hsame_symm sameExportedA)
      (hsame_trans rows.right.right.right sameExportedB)
  exact And.intro ledgerA (And.intro ledgerB sameExported)

end BEDC.Derived.SheafUp
