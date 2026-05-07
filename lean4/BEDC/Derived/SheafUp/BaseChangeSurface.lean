import BEDC.Derived.SheafUp.CoverPullback

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

theorem SheafBaseChange_common_refinement_projection
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
                        hsame germ sourceCoverGerm ∧ hsame pulledGermA pulledGermB ∧
                          hsame targetOpen pulledOpen := by
  intro coverLedger sameMember sameOverlap sourceRow ledgerA ledgerB sameGerm sameRepresented
    samePulled pulledRowA pulledRowB
  have coverPullback :=
    SheafBHistCoverNerveLedger_base_change_cover_pullback coverLedger sameMember
      sameOverlap sourceRow
  have pulledA :=
    SheafBHistPointGermLedger_base_change_gluing_pullback ledgerA sameRepresented samePulled
      pulledRowA
  have pulledB :=
    SheafBHistPointGermLedger_base_change_gluing_pullback ledgerB sameRepresented samePulled
      pulledRowB
  have samePulledGerms : hsame pulledGermA pulledGermB :=
    hsame_trans (hsame_symm pulledA.right.left)
      (hsame_trans sameGerm pulledB.right.left)
  have comparison :
      SheafBHistPointGermComparison point pulledOpen sectionA pulledGermA pulledOpen sectionB
        pulledGermB pulledOpen :=
    (SheafBHistPointGermLedger_common_open_comparison pulledA.left pulledB.left
      samePulledGerms).left
  exact And.intro coverPullback.left
    (And.intro comparison
      (And.intro coverPullback.right
        (And.intro samePulledGerms pulledA.right.right)))

end BEDC.Derived.SheafUp
