import BEDC.Derived.SheafUp.DownstreamProjection

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem SheafRootNameCertCarrierClassifier_fields
    {point openHist sectionHist germ restrictedOpen restrictedGerm : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen sectionHist restrictedGerm ->
          SemanticNameCert
              (fun endpoint : BHist =>
                SheafBHistPointGermLedger point openHist sectionHist endpoint)
              (fun endpoint : BHist =>
                SheafBHistPointGermLedger point openHist sectionHist endpoint)
              (fun endpoint : BHist =>
                SheafBHistPointGermLedger point openHist sectionHist endpoint)
              hsame ∧
            SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
              hsame germ restrictedGerm := by
  intro ledger sameOpen restrictedRow
  have cert :
      SemanticNameCert
        (fun endpoint : BHist => SheafBHistPointGermLedger point openHist sectionHist endpoint)
        (fun endpoint : BHist => SheafBHistPointGermLedger point openHist sectionHist endpoint)
        (fun endpoint : BHist => SheafBHistPointGermLedger point openHist sectionHist endpoint)
        hsame :=
    SheafRestrictedOpenCarrier_semantic_name_certificate ledger
  have readback :
      SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
        hsame germ restrictedGerm :=
    SheafBHistPointGermLedger_restriction_readback ledger sameOpen restrictedRow
  exact And.intro cert readback

theorem SheafRootSchemeAffineChartProjection_seal
    {point openA routeAB openB routeBC openC routeAC openC' sect germC germC'
      common chartOut : BHist} {sections : List BHist} :
    SheafBHistPointGermLedger point openC sect germC ->
      Cont openA routeAB openB -> Cont openB routeBC openC -> Cont routeAB routeBC routeAC ->
        Cont openA routeAC openC' -> Cont openC' sect germC' ->
          SheafSchemeChartGluingTrace point common sections chartOut ->
            SheafBHistPointGermLedger point openC' sect germC' ∧ hsame openC openC' ∧
              hsame germC germC' ∧ UnaryHistory chartOut := by
  intro ledger routeA routeB routeAB routeDirect sectionDirect chartTrace
  have routeReadback :
      SheafBHistPointGermLedger point openC' sect germC' ∧
        hsame openC openC' ∧ hsame germC germC' :=
    SheafBHistPointGermLedger_route_cont_composition
      ledger routeA routeB routeAB routeDirect sectionDirect
  have chartUnary : UnaryHistory chartOut :=
    SheafSchemeChartGluingTrace_unary_result chartTrace
  exact And.intro routeReadback.left
    (And.intro routeReadback.right.left
      (And.intro routeReadback.right.right chartUnary))

theorem SheafRootTopologyPullbackProjection_seal
    {point openA routeAB openB routeBC openC routeAC openC' sect germC germC'
      pullbackEndpoint : BHist} :
    SheafBHistPointGermLedger point openC sect germC ->
      Cont openA routeAB openB -> Cont openB routeBC openC -> Cont routeAB routeBC routeAC ->
        Cont openA routeAC openC' -> Cont openC' sect germC' ->
          hsame pullbackEndpoint germC' ->
            SheafBHistPointGermLedger point openC' sect germC' ∧ hsame openC openC' ∧
              hsame germC germC' ∧ hsame pullbackEndpoint germC' := by
  intro ledger routeA routeB routeAB routeDirect sectionDirect sameEndpoint
  have routeReadback :
      SheafBHistPointGermLedger point openC' sect germC' ∧
        hsame openC openC' ∧ hsame germC germC' :=
    SheafBHistPointGermLedger_route_cont_composition
      ledger routeA routeB routeAB routeDirect sectionDirect
  exact And.intro routeReadback.left
    (And.intro routeReadback.right.left
      (And.intro routeReadback.right.right sameEndpoint))

theorem SheafRootRingedSpaceConsumerProjection_scope
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
        restrictedGermA restrictedGermB chartEndpoint ->
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                restrictedOpen sectionB restrictedGermB restrictedOpen ∧
                SheafRootFaceRead restrictedOpen restrictedGermA .localityGluingRefinement ∧
                  SheafRootFaceRead restrictedOpen restrictedGermB .localityGluingRefinement ∧
                    hsame chartEndpoint restrictedGermB := by
  intro scope
  have carrierRows :=
    SheafDownstreamConsumer_carrier_scope (point := point) (openHist := openHist)
      (sectionA := sectionA) (sectionB := sectionB) (germA := germA) (germB := germB)
      (restrictedOpen := restrictedOpen) (restrictedGermA := restrictedGermA)
      (restrictedGermB := restrictedGermB) (chartEndpoint := chartEndpoint) scope
  have faceRows :=
    SheafRootFaceRead_downstream_projection_separation (point := point)
      (openHist := openHist) (sectionA := sectionA) (sectionB := sectionB)
      (germA := germA) (germB := germB) (restrictedOpen := restrictedOpen)
      (restrictedGermA := restrictedGermA) (restrictedGermB := restrictedGermB)
      (chartEndpoint := chartEndpoint) scope
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    (SheafBHistPointGermLedger_common_open_comparison carrierRows.left
      carrierRows.right.left carrierRows.right.right.right.right.left).left
  exact And.intro carrierRows.left
    (And.intro carrierRows.right.left
      (And.intro faceRows.left
        (And.intro faceRows.right.left
          (And.intro comparison
            (And.intro faceRows.right.right.left
              (And.intro faceRows.right.right.right.left
                faceRows.right.right.right.right))))))

end BEDC.Derived.SheafUp
