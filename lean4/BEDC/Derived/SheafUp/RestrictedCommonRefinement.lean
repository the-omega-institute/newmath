import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafRestrictedCommonRefinement_pullback_compatibility
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB ->
          hsame openHist restrictedOpen ->
            Cont restrictedOpen sectionA restrictedGermA ->
              Cont restrictedOpen sectionB restrictedGermB ->
                Cont restrictedOpen sectionA globalA ->
                  Cont restrictedOpen sectionB globalB ->
                    SheafBHistPointGermComparison point restrictedOpen sectionA globalA
                        restrictedOpen sectionB globalB restrictedOpen ∧
                      hsame globalA globalB := by
  intro ledgerA ledgerB sameGerm sameOpen _restrictedA _restrictedB globalRowA globalRowB
  have readbackA :
      SheafBHistPointGermLedger point restrictedOpen sectionA globalA ∧
        hsame germA globalA :=
    SheafBHistPointGermLedger_restriction_readback ledgerA sameOpen globalRowA
  have readbackB :
      SheafBHistPointGermLedger point restrictedOpen sectionB globalB ∧
        hsame germB globalB :=
    SheafBHistPointGermLedger_restriction_readback ledgerB sameOpen globalRowB
  have sameGlobal : hsame globalA globalB :=
    hsame_trans (hsame_symm readbackA.right)
      (hsame_trans sameGerm readbackB.right)
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA globalA restrictedOpen
        sectionB globalB restrictedOpen :=
    (SheafBHistPointGermLedger_common_open_comparison
      readbackA.left readbackB.left sameGlobal).left
  exact And.intro comparison sameGlobal

end BEDC.Derived.SheafUp
