import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafRootRestrictionRefinement_obligation
    {point openA openB openC sectionHist germA germB germC route routeTarget : BHist} :
    SheafBHistPointGermLedger point openA sectionHist germA ->
      hsame openA openB ->
        Cont openB sectionHist germB ->
          hsame openB openC ->
            Cont openC sectionHist germC ->
              Cont openB route routeTarget ->
                hsame routeTarget openB ->
                  SheafBHistPointGermLedger point openC sectionHist germC ∧
                    hsame germA germC ∧ hsame route BHist.Empty := by
  intro ledger sameAB rowB sameBC rowC routeRow routeBoundary
  have refinement :
      SheafBHistPointGermLedger point openC sectionHist germC ∧
        hsame germA germC ∧ hsame germB germC :=
    SheafBHistPointGermLedger_refinement_composition ledger sameAB rowB sameBC rowC
  have routeUnit : hsame route BHist.Empty := by
    cases routeBoundary
    exact cont_right_unit_unique routeRow
  exact And.intro refinement.left (And.intro refinement.right.left routeUnit)

end BEDC.Derived.SheafUp
