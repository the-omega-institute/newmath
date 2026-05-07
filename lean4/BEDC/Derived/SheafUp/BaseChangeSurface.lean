import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafBHistPointGermLedger_base_change_gluing_pullback
    {point targetOpen representedOpen pulledOpen sectionHist germ pulledGerm : BHist} :
    SheafBHistPointGermLedger point targetOpen sectionHist germ ->
      hsame targetOpen representedOpen -> hsame representedOpen pulledOpen ->
        Cont pulledOpen sectionHist pulledGerm ->
          SheafBHistPointGermLedger point pulledOpen sectionHist pulledGerm ∧
            hsame germ pulledGerm ∧ hsame targetOpen pulledOpen := by
  intro ledger sameRepresented samePulled pulledRow
  have sameTargetPulled : hsame targetOpen pulledOpen :=
    hsame_trans sameRepresented samePulled
  have readback :
      SheafBHistPointGermLedger point pulledOpen sectionHist pulledGerm ∧
        hsame germ pulledGerm :=
    SheafBHistPointGermLedger_restriction_readback ledger sameTargetPulled pulledRow
  exact And.intro readback.left (And.intro readback.right sameTargetPulled)

theorem SheafBHistPointGermLedger_base_change_gluing_pullback_composition
    {point targetOpen representedOpen pulledOpen finalOpen sectionHist germ pulledGerm
      finalGerm directGerm : BHist} :
    SheafBHistPointGermLedger point targetOpen sectionHist germ ->
      hsame targetOpen representedOpen -> hsame representedOpen pulledOpen ->
        Cont pulledOpen sectionHist pulledGerm -> hsame pulledOpen finalOpen ->
          Cont finalOpen sectionHist finalGerm -> Cont finalOpen sectionHist directGerm ->
            SheafBHistPointGermLedger point finalOpen sectionHist directGerm ∧
              hsame germ directGerm ∧ hsame pulledGerm finalGerm ∧
                hsame finalGerm directGerm := by
  intro ledger sameRepresented samePulled pulledRow sameFinal finalRow directRow
  have pulledReadback :
      SheafBHistPointGermLedger point pulledOpen sectionHist pulledGerm ∧
        hsame germ pulledGerm ∧ hsame targetOpen pulledOpen :=
    SheafBHistPointGermLedger_base_change_gluing_pullback
      ledger sameRepresented samePulled pulledRow
  have finalReadback :
      SheafBHistPointGermLedger point finalOpen sectionHist finalGerm ∧
        hsame pulledGerm finalGerm :=
    SheafBHistPointGermLedger_restriction_readback pulledReadback.left sameFinal finalRow
  have directLedger : SheafBHistPointGermLedger point finalOpen sectionHist directGerm :=
    And.intro finalReadback.left.left
      (And.intro finalReadback.left.right.left directRow)
  have sameFinalDirect : hsame finalGerm directGerm :=
    cont_deterministic finalRow directRow
  have sameGermDirect : hsame germ directGerm :=
    hsame_trans pulledReadback.right.left
      (hsame_trans finalReadback.right sameFinalDirect)
  exact And.intro directLedger
    (And.intro sameGermDirect
      (And.intro finalReadback.right sameFinalDirect))

end BEDC.Derived.SheafUp
