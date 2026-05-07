import BEDC.Derived.SheafUp.CoverPullback

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

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

theorem SheafBaseChange_name_certificate
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
                    SemanticNameCert
                      (fun endpoint : BHist =>
                        SheafBHistPointGermLedger point pulledOpen sectionA endpoint)
                      (fun endpoint : BHist =>
                        SheafBHistPointGermLedger point pulledOpen sectionA endpoint)
                      (fun endpoint : BHist =>
                        SheafBHistPointGermLedger point pulledOpen sectionA endpoint ∧
                          (exists paired : BHist,
                            SheafBHistPointGermLedger point pulledOpen sectionB paired ∧
                              hsame endpoint paired) ∧
                            SheafBHistCoverNerveLedger ambient sourceMember sourceOverlap route
                              sourceCoverGerm)
                      hsame := by
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
  have pulledA :
      SheafBHistPointGermLedger point pulledOpen sectionA pulledGermA ∧
        hsame germA pulledGermA ∧ hsame targetOpen pulledOpen :=
    SheafBHistPointGermLedger_base_change_gluing_pullback ledgerA sameRepresented samePulled
      pulledRowA
  have pulledB :
      SheafBHistPointGermLedger point pulledOpen sectionB pulledGermB ∧
        hsame germB pulledGermB ∧ hsame targetOpen pulledOpen :=
    SheafBHistPointGermLedger_base_change_gluing_pullback ledgerB sameRepresented samePulled
      pulledRowB
  have pulledLedgerA :
      SheafBHistPointGermLedger point pulledOpen sectionA pulledGermA :=
    pulledA.left
  have pulledLedgerB :
      SheafBHistPointGermLedger point pulledOpen sectionB pulledGermB :=
    pulledB.left
  have samePulledGerms : hsame pulledGermA pulledGermB :=
    projection.right.right.right.left
  constructor
  · constructor
    · exact Exists.intro pulledGermA pulledLedgerA
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
  · intro endpoint source
    have sameEndpointPulledA : hsame endpoint pulledGermA :=
      cont_deterministic source.right.right pulledRowA
    exact And.intro source
      (And.intro
        (Exists.intro pulledGermB
          (And.intro pulledLedgerB
            (hsame_trans sameEndpointPulledA samePulledGerms)))
        projection.left)

end BEDC.Derived.SheafUp
