import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafRefinedCover_exactness_obligation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              hsame restrictedGermA restrictedGermB ->
                Cont openHist sectionA globalA ->
                  Cont openHist sectionB globalB ->
                    SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                      SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                        SheafBHistPointGermComparison point restrictedOpen sectionA
                          restrictedGermA restrictedOpen sectionB restrictedGermB
                          restrictedOpen ∧
                          hsame globalA globalB := by
  intro ledgerA ledgerB sameOpen restrictedA restrictedB sameRestricted globalACont
    globalBCont
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
    (SheafBHistPointGermLedger_common_open_comparison readbackA.left readbackB.left
      sameRestricted).left
  have sameGlobalA : hsame germA globalA :=
    cont_deterministic ledgerA.right.right globalACont
  have sameGlobalB : hsame germB globalB :=
    cont_deterministic ledgerB.right.right globalBCont
  have sameGlobal : hsame globalA globalB :=
    hsame_trans (hsame_symm sameGlobalA)
      (hsame_trans readbackA.right
        (hsame_trans sameRestricted
          (hsame_trans (hsame_symm readbackB.right) sameGlobalB)))
  exact And.intro readbackA.left
    (And.intro readbackB.left (And.intro comparison sameGlobal))

end BEDC.Derived.SheafUp
