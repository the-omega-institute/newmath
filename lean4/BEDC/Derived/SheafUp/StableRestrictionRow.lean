import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafStableRestrictionRow
    (point openHist sectionHist germ restrictedOpen restrictedGerm : BHist) : Prop :=
  SheafBHistPointGermLedger point openHist sectionHist germ ∧
    hsame openHist restrictedOpen ∧ Cont restrictedOpen sectionHist restrictedGerm

theorem SheafStableRestrictionRow_transport
    {point openHist sectionHist germ restrictedOpen restrictedGerm : BHist} :
    SheafStableRestrictionRow point openHist sectionHist germ restrictedOpen restrictedGerm ->
      SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
        hsame germ restrictedGerm ∧ UnaryHistory restrictedOpen := by
  intro row
  have readback :
      SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
        hsame germ restrictedGerm :=
    SheafBHistPointGermLedger_restriction_readback row.left row.right.left row.right.right
  exact And.intro readback.left (And.intro readback.right readback.left.right.left)

theorem SheafStableRestrictionRow_restricted_comparison_readback
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              hsame restrictedGermA restrictedGermB ->
                SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                    restrictedOpen sectionB restrictedGermB restrictedOpen ∧
                  hsame germA germB := by
  intro ledgerA ledgerB sameOpen restrictedA restrictedB sameRestricted
  have readbackA :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        hsame germA restrictedGermA :=
    SheafBHistPointGermLedger_restriction_readback ledgerA sameOpen restrictedA
  have readbackB :
      SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
        hsame germB restrictedGermB :=
    SheafBHistPointGermLedger_restriction_readback ledgerB sameOpen restrictedB
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    (SheafBHistPointGermLedger_common_open_comparison
      readbackA.left readbackB.left sameRestricted).left
  have sameOriginal : hsame germA germB :=
    hsame_trans readbackA.right (hsame_trans sameRestricted (hsame_symm readbackB.right))
  exact And.intro comparison sameOriginal

theorem SheafBHistPointGermLedger_restriction_stability_obligation
    {point openHist sectionHist germ midOpen midGerm restrictedOpen restrictedGerm : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      hsame openHist midOpen ->
        Cont midOpen sectionHist midGerm ->
          hsame midOpen restrictedOpen ->
            Cont restrictedOpen sectionHist restrictedGerm ->
              SheafBHistPointGermLedger point midOpen sectionHist midGerm ∧
                SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
                  hsame germ midGerm ∧ hsame midGerm restrictedGerm ∧
                    hsame germ restrictedGerm := by
  intro ledger sameMid midRow sameRestricted restrictedRow
  have midReadback :
      SheafBHistPointGermLedger point midOpen sectionHist midGerm ∧ hsame germ midGerm :=
    SheafBHistPointGermLedger_restriction_readback ledger sameMid midRow
  have restrictedReadback :
      SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
        hsame midGerm restrictedGerm :=
    SheafBHistPointGermLedger_restriction_readback midReadback.left sameRestricted restrictedRow
  have sameOriginalRestricted : hsame germ restrictedGerm :=
    hsame_trans midReadback.right restrictedReadback.right
  exact And.intro midReadback.left
    (And.intro restrictedReadback.left
      (And.intro midReadback.right
        (And.intro restrictedReadback.right sameOriginalRestricted)))

end BEDC.Derived.SheafUp
