import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem SheafConsumerAccessTrace_refinement_obligation {root : BHist}
    {cover refined : List BHist} :
    SheafConsumerAccessTrace root cover ->
      (forall row : BHist, List.Mem row refined -> List.Mem row cover) ->
        UnaryHistory root ∧ SheafConsumerAccessTrace root refined := by
  intro coverTrace membershipInclusion
  exact And.intro coverTrace.left
    (And.intro coverTrace.left
      (by
        intro row rowMem
        exact coverTrace.right row (membershipInclusion row rowMem)))

theorem SheafRootExport_stability_exactness_package
    {root ambient member overlap route germ point openHist sectionA sectionB germA germB
      restrictedOpen restrictedGermA restrictedGermB : BHist} {trace : List BHist} :
    SheafConsumerAccessTrace root trace ->
      SheafBHistCoverNerveLedger ambient member overlap route germ ->
        SheafBHistPointGermLedger point openHist sectionA germA ->
          SheafBHistPointGermLedger point openHist sectionB germB ->
            hsame germA germB ->
              hsame openHist restrictedOpen ->
                Cont restrictedOpen sectionA restrictedGermA ->
                  Cont restrictedOpen sectionB restrictedGermB ->
                    SheafConsumerAccessTrace root trace ∧
                      SheafBHistCoverNerveLedger ambient member overlap route germ ∧
                        SheafBHistPointGermLedger point restrictedOpen sectionA
                          restrictedGermA ∧
                          SheafBHistPointGermLedger point restrictedOpen sectionB
                            restrictedGermB ∧
                            SheafBHistPointGermComparison point restrictedOpen sectionA
                              restrictedGermA restrictedOpen sectionB restrictedGermB
                              restrictedOpen ∧
                              hsame restrictedGermA restrictedGermB := by
  intro traceRows coverLedger ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    (SheafBHistPointGermLedger_common_open_comparison
      descent.left descent.right.left descent.right.right).left
  exact And.intro traceRows
    (And.intro coverLedger
      (And.intro descent.left
        (And.intro descent.right.left
          (And.intro comparison descent.right.right))))

theorem SheafRootUnblock_restriction_stability_rows
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB route routeTarget routeGerm : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              Cont restrictedOpen route routeTarget -> hsame routeTarget restrictedOpen ->
                Cont routeTarget sectionA routeGerm ->
                  SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                    SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                      hsame restrictedGermA restrictedGermB ∧ hsame route BHist.Empty ∧
                        SheafBHistPointGermLedger point routeTarget sectionA routeGerm ∧
                          hsame germA routeGerm := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB routeRow sameTarget routeGermRow
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have routeStable :
      hsame route BHist.Empty ∧
        SheafBHistPointGermLedger point routeTarget sectionA routeGerm ∧
          hsame germA routeGerm :=
    SheafBHistPointGermLedger_route_history_stability
      ledgerA sameOpen routeRow sameTarget routeGermRow
  exact And.intro descent.left
    (And.intro descent.right.left
      (And.intro descent.right.right
        (And.intro routeStable.left routeStable.right)))

theorem SheafConsumerAccessTrace_composite_exhaustion {root : BHist}
    (rootUnary : UnaryHistory root) {traces : List (List BHist)} :
    (forall trace : List BHist, List.Mem trace traces -> SheafConsumerAccessTrace root trace) ->
      SheafConsumerAccessTrace root (traces.foldr List.append []) := by
  intro traceRows
  induction traces with
  | nil =>
      exact And.intro rootUnary
        (by
          intro row rowMem
          cases rowMem)
  | cons trace rest ih =>
      have headTrace : SheafConsumerAccessTrace root trace :=
        traceRows trace (List.Mem.head rest)
      have restRows :
          forall restTrace : List BHist, List.Mem restTrace rest ->
            SheafConsumerAccessTrace root restTrace := by
        intro restTrace restMem
        exact traceRows restTrace (List.Mem.tail trace restMem)
      have restTrace : SheafConsumerAccessTrace root (rest.foldr List.append []) :=
        ih restRows
      exact (SheafConsumerAccessTrace_append_closed headTrace restTrace).right

theorem SheafRootUnblockRestrictionStability_semantic_name_certificate
    {point openHist sectionHist germ restrictedOpen route routeTarget restrictedGerm : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen route routeTarget ->
          hsame routeTarget restrictedOpen ->
            Cont routeTarget sectionHist restrictedGerm ->
              SemanticNameCert
                  (fun endpoint : BHist =>
                    SheafBHistPointGermLedger point routeTarget sectionHist endpoint)
                  (fun endpoint : BHist =>
                    SheafBHistPointGermLedger point routeTarget sectionHist endpoint)
                  (fun endpoint : BHist =>
                    SheafBHistPointGermLedger point routeTarget sectionHist endpoint)
                  hsame ∧
                hsame route BHist.Empty ∧
                  SheafBHistPointGermLedger point routeTarget sectionHist restrictedGerm ∧
                    hsame germ restrictedGerm := by
  intro ledger sameOpen routeRow sameTarget restrictedRow
  have stable :
      hsame route BHist.Empty ∧
        SheafBHistPointGermLedger point routeTarget sectionHist restrictedGerm ∧
          hsame germ restrictedGerm :=
    SheafBHistPointGermLedger_route_history_stability
      ledger sameOpen routeRow sameTarget restrictedRow
  have cert :
      SemanticNameCert
        (fun endpoint : BHist => SheafBHistPointGermLedger point routeTarget sectionHist endpoint)
        (fun endpoint : BHist => SheafBHistPointGermLedger point routeTarget sectionHist endpoint)
        (fun endpoint : BHist => SheafBHistPointGermLedger point routeTarget sectionHist endpoint)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro restrictedGerm stable.right.left
      · intro endpoint _carrier
        exact hsame_refl endpoint
      · intro endpoint endpoint' same
        exact hsame_symm same
      · intro endpoint endpoint' endpoint'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro endpoint endpoint' same carrier
        exact And.intro carrier.left
          (And.intro carrier.right.left
            (cont_result_hsame_transport carrier.right.right same))
    · intro _endpoint source
      exact source
    · intro _endpoint source
      exact source
  exact And.intro cert
    (And.intro stable.left
      (And.intro stable.right.left stable.right.right))

end BEDC.Derived.SheafUp
