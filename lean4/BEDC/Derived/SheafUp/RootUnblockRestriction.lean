import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafRootUnblock_restriction_stability_surface
    {point openHist sectionHist germ restrictedOpen restrictedGerm route routeTarget
      routeGerm : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen sectionHist restrictedGerm ->
          Cont restrictedOpen route routeTarget ->
            hsame routeTarget restrictedOpen ->
              Cont routeTarget sectionHist routeGerm ->
                SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
                  SheafBHistPointGermLedger point routeTarget sectionHist routeGerm ∧
                    hsame germ restrictedGerm ∧ hsame germ routeGerm ∧
                      hsame route BHist.Empty := by
  intro ledger sameOpen restrictedRow routeRow sameTarget routeGermRow
  have restricted :
      SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
        hsame germ restrictedGerm :=
    SheafBHistPointGermLedger_restriction_readback ledger sameOpen restrictedRow
  have routeStable :
      hsame route BHist.Empty ∧
        SheafBHistPointGermLedger point routeTarget sectionHist routeGerm ∧
          hsame germ routeGerm :=
    SheafBHistPointGermLedger_route_history_stability
      ledger sameOpen routeRow sameTarget routeGermRow
  exact And.intro restricted.left
    (And.intro routeStable.right.left
      (And.intro restricted.right
        (And.intro routeStable.right.right routeStable.left)))

end BEDC.Derived.SheafUp
