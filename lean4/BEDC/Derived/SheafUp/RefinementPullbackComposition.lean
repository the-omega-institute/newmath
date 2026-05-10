import BEDC.Derived.SheafUp
import BEDC.Derived.SheafUp.CoverDescent

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafRefinementPullback_composition
    {point openA openB openC sectionHist germA germB germC directGerm : BHist} :
    SheafBHistPointGermLedger point openA sectionHist germA ->
      hsame openA openB ->
        Cont openB sectionHist germB ->
          hsame openB openC ->
            Cont openC sectionHist germC ->
              Cont openC sectionHist directGerm ->
                SheafBHistPointGermLedger point openC sectionHist directGerm ∧
                  hsame germC directGerm ∧ hsame germA directGerm := by
  intro ledger sameAB rowB sameBC rowC directRow
  have composed :
      SheafBHistPointGermLedger point openC sectionHist germC ∧
        hsame germA germC ∧ hsame germB germC :=
    SheafBHistPointGermLedger_refinement_composition ledger sameAB rowB sameBC rowC
  have directLedger :
      SheafBHistPointGermLedger point openC sectionHist directGerm :=
    And.intro composed.left.left (And.intro composed.left.right.left directRow)
  have sameDirect : hsame germC directGerm :=
    cont_deterministic rowC directRow
  exact And.intro directLedger
    (And.intro sameDirect (hsame_trans composed.right.left sameDirect))

theorem SheafRootCoverNerve_downstream_coverage
    {ambient member overlap route germ point openHist sectionA sectionB germA germB
      restrictedOpen restrictedGermA restrictedGermB : BHist} :
    SheafBHistCoverNerveLedger ambient member overlap route germ ->
      SheafBHistPointGermLedger point openHist sectionA germA ->
        SheafBHistPointGermLedger point openHist sectionB germB ->
          hsame germA germB ->
            hsame openHist restrictedOpen ->
              Cont restrictedOpen sectionA restrictedGermA ->
                Cont restrictedOpen sectionB restrictedGermB ->
                  SheafRootFaceRead member overlap .coverMembership ∧
                    SheafRootFaceRead overlap germ .restrictionRoute ∧
                      SheafBHistPointGermComparison point restrictedOpen sectionA
                        restrictedGermA restrictedOpen sectionB restrictedGermB
                        restrictedOpen ∧
                        hsame restrictedGermA restrictedGermB := by
  intro coverLedger ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have coverExact :
      SheafRootFaceRead member overlap .coverMembership ∧
        SheafRootFaceRead overlap germ .restrictionRoute ∧
          UnaryHistory ambient ∧ UnaryHistory member ∧ UnaryHistory overlap :=
    SheafRootCoverDescent_carrier_exactness coverLedger
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
          restrictedOpen sectionB restrictedGermB restrictedOpen ∧
        Cont restrictedOpen sectionA restrictedGermA ∧
          Cont restrictedOpen sectionB restrictedGermB :=
    SheafBHistPointGermLedger_common_open_comparison
      descent.left descent.right.left descent.right.right
  exact And.intro coverExact.left
    (And.intro coverExact.right.left
      (And.intro comparison.left descent.right.right))

end BEDC.Derived.SheafUp
