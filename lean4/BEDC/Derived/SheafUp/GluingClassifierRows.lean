import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

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

end BEDC.Derived.SheafUp
