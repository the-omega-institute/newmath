import BEDC.Derived.SheafUp.BaseChangeSurface
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

def SheafRootConsumerProjectionSeal
    (point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint openA routeAB openB routeBC openC routeAC openC' sect
      germC germC' pullbackEndpoint : BHist) (sections : List BHist) : Prop :=
  SheafDownstreamConsumerScope point openHist sectionA sectionB germA germB restrictedOpen
      restrictedGermA restrictedGermB chartEndpoint ∧
    SheafBHistPointGermLedger point openC sect germC ∧
      Cont openA routeAB openB ∧
        Cont openB routeBC openC ∧
          Cont routeAB routeBC routeAC ∧
            Cont openA routeAC openC' ∧
              Cont openC' sect germC' ∧
                hsame pullbackEndpoint germC' ∧
                  SheafSchemeChartGluingTrace point restrictedOpen sections chartEndpoint

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

theorem SheafRootConsumerProjectionSeal_projection_rows
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint openA routeAB openB routeBC openC routeAC openC' sect
      germC germC' pullbackEndpoint : BHist} {sections : List BHist} :
    SheafRootConsumerProjectionSeal point openHist sectionA sectionB germA germB
        restrictedOpen restrictedGermA restrictedGermB chartEndpoint openA routeAB openB
        routeBC openC routeAC openC' sect germC germC' pullbackEndpoint sections ->
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
          restrictedOpen sectionB restrictedGermB restrictedOpen ∧
        SheafRootFaceRead restrictedOpen restrictedGermA .localityGluingRefinement ∧
          SheafRootFaceRead restrictedOpen restrictedGermB .localityGluingRefinement ∧
            SheafBHistPointGermLedger point openC' sect germC' ∧
              hsame openC openC' ∧ hsame germC germC' ∧
                hsame pullbackEndpoint germC' ∧ UnaryHistory chartEndpoint := by
  intro hseal
  have ringed :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          Cont restrictedOpen sectionA restrictedGermA ∧
            Cont restrictedOpen sectionB restrictedGermB ∧
              SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                restrictedOpen sectionB restrictedGermB restrictedOpen ∧
                SheafRootFaceRead restrictedOpen restrictedGermA .localityGluingRefinement ∧
                  SheafRootFaceRead restrictedOpen restrictedGermB .localityGluingRefinement ∧
                    hsame chartEndpoint restrictedGermB :=
    SheafRootRingedSpaceConsumerProjection_scope
      (point := point) (openHist := openHist) (sectionA := sectionA)
      (sectionB := sectionB) (germA := germA) (germB := germB)
      (restrictedOpen := restrictedOpen) (restrictedGermA := restrictedGermA)
      (restrictedGermB := restrictedGermB) (chartEndpoint := chartEndpoint) hseal.left
  have scheme :
      SheafBHistPointGermLedger point openC' sect germC' ∧ hsame openC openC' ∧
        hsame germC germC' ∧ UnaryHistory chartEndpoint :=
    SheafRootSchemeAffineChartProjection_seal
      (point := point) (openA := openA) (routeAB := routeAB) (openB := openB)
      (routeBC := routeBC) (openC := openC) (routeAC := routeAC) (openC' := openC')
      (sect := sect) (germC := germC) (germC' := germC') (common := restrictedOpen)
      (chartOut := chartEndpoint) (sections := sections) hseal.right.left
      hseal.right.right.left hseal.right.right.right.left hseal.right.right.right.right.left
      hseal.right.right.right.right.right.left hseal.right.right.right.right.right.right.left
      hseal.right.right.right.right.right.right.right.right
  exact And.intro ringed.right.right.right.right.left
    (And.intro ringed.right.right.right.right.right.left
      (And.intro ringed.right.right.right.right.right.right.left
        (And.intro scheme.left
          (And.intro scheme.right.left
            (And.intro scheme.right.right.left
              (And.intro hseal.right.right.right.right.right.right.right.left
                scheme.right.right.right))))))

theorem SheafRootConsumerPullbackProjection_base_change_face
    {ambient member overlap route germ sourceMember sourceOverlap sourceCoverGerm point targetOpen
      representedOpen pulledOpen sectionA sectionB germA germB pulledGermA pulledGermB :
        BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      hsame member sourceMember -> hsame overlap sourceOverlap ->
        Cont sourceOverlap route sourceCoverGerm ->
          SheafBHistPointGermLedger point targetOpen sectionA germA ->
            SheafBHistPointGermLedger point targetOpen sectionB germB ->
              hsame germA germB -> hsame targetOpen representedOpen ->
                hsame representedOpen pulledOpen -> Cont pulledOpen sectionA pulledGermA ->
                  Cont pulledOpen sectionB pulledGermB ->
                    SheafBHistCoverNerveLedger ambient sourceMember sourceOverlap route
                        sourceCoverGerm ∧
                      SheafBHistPointGermComparison point pulledOpen sectionA pulledGermA
                        pulledOpen sectionB pulledGermB pulledOpen ∧
                        SheafRootFaceRead pulledOpen pulledGermA
                          .localityGluingRefinement ∧
                          SheafRootFaceRead pulledOpen pulledGermB
                            .localityGluingRefinement ∧
                            hsame targetOpen pulledOpen := by
  intro coverLedger sameMember sameOverlap sourceRow ledgerA ledgerB sameGerm sameRepresented
    samePulled pulledRowA pulledRowB
  have projection :
      SheafBHistCoverNerveLedger ambient sourceMember sourceOverlap route sourceCoverGerm ∧
        SheafBHistPointGermComparison point pulledOpen sectionA pulledGermA pulledOpen sectionB
          pulledGermB pulledOpen ∧
          hsame germ sourceCoverGerm ∧ hsame pulledGermA pulledGermB ∧
            hsame targetOpen pulledOpen :=
    SheafBaseChange_common_refinement_projection coverLedger sameMember sameOverlap sourceRow
      ledgerA ledgerB sameGerm sameRepresented samePulled pulledRowA pulledRowB
  have readA :
      SheafRootFaceRead pulledOpen pulledGermA .localityGluingRefinement :=
    SheafRootFaceRead.localityGluingRefinement pulledRowA pulledRowB
      projection.right.right.right.left
  have readB :
      SheafRootFaceRead pulledOpen pulledGermB .localityGluingRefinement :=
    SheafRootFaceRead.localityGluingRefinement pulledRowB pulledRowA
      (hsame_symm projection.right.right.right.left)
  exact And.intro projection.left
    (And.intro projection.right.left
      (And.intro readA
        (And.intro readB projection.right.right.right.right)))

end BEDC.Derived.SheafUp
