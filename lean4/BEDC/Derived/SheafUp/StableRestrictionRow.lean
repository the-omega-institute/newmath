import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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

end BEDC.Derived.SheafUp
