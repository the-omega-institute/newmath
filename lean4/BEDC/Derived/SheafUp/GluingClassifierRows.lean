import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem SheafBHistPointGermLedger_gluing_uniqueness_from_locality
    {point openHist sectionA sectionB germA germB common commonGermA commonGermB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame openHist common ->
          Cont common sectionA commonGermA ->
            Cont common sectionB commonGermB ->
              hsame commonGermA commonGermB -> hsame germA germB := by
  intro ledgerA ledgerB sameOpen commonRowA commonRowB sameCommonGerms
  have readbackA :
      SheafBHistPointGermLedger point common sectionA commonGermA ∧
        hsame germA commonGermA :=
    SheafBHistPointGermLedger_restriction_readback ledgerA sameOpen commonRowA
  have readbackB :
      SheafBHistPointGermLedger point common sectionB commonGermB ∧
        hsame germB commonGermB :=
    SheafBHistPointGermLedger_restriction_readback ledgerB sameOpen commonRowB
  exact hsame_trans readbackA.right
    (hsame_trans sameCommonGerms (hsame_symm readbackB.right))

theorem SheafGluingCompatibleFamily_stability_semantic_certificate
    {point openHist sectionA sectionB germA germB memberOpen memberSectA memberSectB
      memberGermA memberGermB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> UnaryHistory memberOpen -> hsame openHist memberOpen ->
          hsame sectionA memberSectA -> hsame sectionB memberSectB ->
            Cont memberOpen memberSectA memberGermA ->
              Cont memberOpen memberSectB memberGermB ->
                SheafBHistPointGermComparison point memberOpen memberSectA memberGermA
                    memberOpen memberSectB memberGermB memberOpen ∧
                  SemanticNameCert
                    (fun endpoint : BHist =>
                      SheafBHistPointGermLedger point memberOpen memberSectA endpoint)
                    (fun endpoint : BHist =>
                      SheafBHistPointGermLedger point memberOpen memberSectA endpoint)
                    (fun endpoint : BHist =>
                      SheafBHistPointGermLedger point memberOpen memberSectA endpoint)
                    hsame ∧
                    hsame memberGermA memberGermB := by
  intro ledgerA ledgerB sameGerm memberOpenUnary sameOpen sameSectA sameSectB memberRowA
    memberRowB
  have memberReadbackA :
      SheafBHistPointGermLedger point memberOpen memberSectA memberGermA ∧
        hsame germA memberGermA :=
    SheafBHistPointGermLedger_gluing_readback ledgerA memberOpenUnary sameOpen sameSectA
      memberRowA
  have memberReadbackB :
      SheafBHistPointGermLedger point memberOpen memberSectB memberGermB ∧
        hsame germB memberGermB :=
    SheafBHistPointGermLedger_gluing_readback ledgerB memberOpenUnary sameOpen sameSectB
      memberRowB
  have sameMemberGerms : hsame memberGermA memberGermB :=
    hsame_trans (hsame_symm memberReadbackA.right)
      (hsame_trans sameGerm memberReadbackB.right)
  have comparison :
      SheafBHistPointGermComparison point memberOpen memberSectA memberGermA memberOpen
        memberSectB memberGermB memberOpen :=
    (SheafBHistPointGermLedger_common_open_comparison
      memberReadbackA.left memberReadbackB.left sameMemberGerms).left
  have cert :
      SemanticNameCert
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point memberOpen memberSectA endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point memberOpen memberSectA endpoint)
        (fun endpoint : BHist =>
          SheafBHistPointGermLedger point memberOpen memberSectA endpoint)
        hsame :=
    SheafRestrictedOpenCarrier_semantic_name_certificate memberReadbackA.left
  exact And.intro comparison (And.intro cert sameMemberGerms)

theorem SheafBHistPointGermComparison_restriction_classifier_transport
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB : BHist} :
    SheafBHistPointGermComparison point openHist sectionA germA openHist sectionB germB
        openHist ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen sectionA restrictedGermA ->
          Cont restrictedOpen sectionB restrictedGermB ->
            SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                restrictedOpen sectionB restrictedGermB restrictedOpen ∧
              hsame germA restrictedGermA ∧ hsame germB restrictedGermB := by
  intro comparison sameOpen restrictedA restrictedB
  have ledgerA : SheafBHistPointGermLedger point openHist sectionA germA :=
    And.intro comparison.left
      (And.intro comparison.right.left comparison.right.right.right.right.right.right.left)
  have ledgerB : SheafBHistPointGermLedger point openHist sectionB germB :=
    And.intro comparison.left
      (And.intro comparison.right.right.left
        comparison.right.right.right.right.right.right.right.left)
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB comparison.right.right.right.right.right.right.right.right sameOpen
      restrictedA restrictedB
  have readbackA :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        hsame germA restrictedGermA :=
    SheafBHistPointGermLedger_restriction_readback ledgerA sameOpen restrictedA
  have readbackB :
      SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
        hsame germB restrictedGermB :=
    SheafBHistPointGermLedger_restriction_readback ledgerB sameOpen restrictedB
  have restrictedComparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    (SheafBHistPointGermLedger_common_open_comparison
      descent.left descent.right.left descent.right.right).left
  exact And.intro restrictedComparison (And.intro readbackA.right readbackB.right)

theorem SheafBHistPointGermComparison_restricted_global_transport_closure
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB : BHist} :
    SheafBHistPointGermComparison point openHist sectionA germA openHist sectionB germB
        openHist ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen sectionA restrictedGermA ->
          Cont restrictedOpen sectionB restrictedGermB ->
            Cont restrictedOpen sectionA globalA ->
              Cont restrictedOpen sectionB globalB ->
                SheafBHistPointGermComparison point restrictedOpen sectionA globalA
                    restrictedOpen sectionB globalB restrictedOpen ∧
                  hsame restrictedGermA globalA ∧ hsame restrictedGermB globalB ∧
                    hsame globalA globalB := by
  intro comparison sameOpen restrictedA restrictedB globalACont globalBCont
  have restricted :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
          restrictedOpen sectionB restrictedGermB restrictedOpen ∧
        hsame germA restrictedGermA ∧ hsame germB restrictedGermB :=
    SheafBHistPointGermComparison_restriction_classifier_transport
      comparison sameOpen restrictedA restrictedB
  have sameRestrictedA : hsame restrictedGermA globalA :=
    cont_deterministic restrictedA globalACont
  have sameRestrictedB : hsame restrictedGermB globalB :=
    cont_deterministic restrictedB globalBCont
  have sameGlobal : hsame globalA globalB :=
    hsame_trans (hsame_symm sameRestrictedA)
      (hsame_trans restricted.left.right.right.right.right.right.right.right.right
        sameRestrictedB)
  have globalLedgerA :
      SheafBHistPointGermLedger point restrictedOpen sectionA globalA :=
    And.intro restricted.left.left
      (And.intro restricted.left.right.left globalACont)
  have globalLedgerB :
      SheafBHistPointGermLedger point restrictedOpen sectionB globalB :=
    And.intro restricted.left.left
      (And.intro restricted.left.right.right.left globalBCont)
  have globalComparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA globalA restrictedOpen
        sectionB globalB restrictedOpen :=
    (SheafBHistPointGermLedger_common_open_comparison
      globalLedgerA globalLedgerB sameGlobal).left
  exact And.intro globalComparison
    (And.intro sameRestrictedA (And.intro sameRestrictedB sameGlobal))

end BEDC.Derived.SheafUp
