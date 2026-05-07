import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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

end BEDC.Derived.SheafUp
