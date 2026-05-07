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

end BEDC.Derived.SheafUp
