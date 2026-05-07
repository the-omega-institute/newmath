import BEDC.Derived.SheafUp.RootRestrictionRefinement
import BEDC.Derived.SheafUp.LocalityGluingCertificate
import BEDC.Derived.SheafUp.RootUnblock
import BEDC.Derived.SheafUp.CommonRefinementSpan

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

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

theorem SheafRootCommonRefinement_route_exactness
    {point common openA openB sectionA sectionB germA germB route routeTarget globalA
      globalB : BHist} :
    SheafDisplayedCommonRefinementSpan point common openA openB sectionA sectionB germA
      germB ->
        Cont common route routeTarget ->
          hsame routeTarget common ->
            Cont routeTarget sectionA globalA ->
              Cont routeTarget sectionB globalB ->
                SheafDisplayedCommonRefinementSpan point routeTarget openA openB sectionA
                    sectionB globalA globalB ∧
                  hsame route BHist.Empty ∧ hsame germA globalA ∧ hsame germB globalB := by
  intro span routeRow sameTarget globalACont globalBCont
  have routeEmpty : hsame route BHist.Empty :=
    cont_right_unit_unique (cont_result_hsame_transport routeRow sameTarget)
  have routeTargetUnary : UnaryHistory routeTarget :=
    unary_transport span.right.left (hsame_symm sameTarget)
  have routeOpenA : hsame routeTarget openA :=
    hsame_trans sameTarget span.right.right.left
  have routeOpenB : hsame routeTarget openB :=
    hsame_trans sameTarget span.right.right.right.left
  have sameGlobalA : hsame germA globalA :=
    cont_respects_hsame (hsame_symm sameTarget) (hsame_refl sectionA)
      span.right.right.right.right.left globalACont
  have sameGlobalB : hsame germB globalB :=
    cont_respects_hsame (hsame_symm sameTarget) (hsame_refl sectionB)
      span.right.right.right.right.right.left globalBCont
  have sameGlobals : hsame globalA globalB :=
    hsame_trans (hsame_symm sameGlobalA)
      (hsame_trans span.right.right.right.right.right.right sameGlobalB)
  exact And.intro
    (And.intro span.left
      (And.intro routeTargetUnary
        (And.intro routeOpenA
          (And.intro routeOpenB
            (And.intro globalACont
              (And.intro globalBCont sameGlobals))))))
    (And.intro routeEmpty (And.intro sameGlobalA sameGlobalB))

end BEDC.Derived.SheafUp
