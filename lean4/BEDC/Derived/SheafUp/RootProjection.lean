import BEDC.Derived.SheafUp

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

end BEDC.Derived.SheafUp
