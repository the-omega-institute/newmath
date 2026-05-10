import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafIndexedCoverCompatibilityLocality_global_rows
    {point openA openB sectA sectB germA germB common globalA globalB : BHist} :
    SheafBHistPointGermComparison point openA sectA germA openB sectB germB common ->
      Cont common sectA globalA ->
        Cont common sectB globalB ->
          hsame germA globalA ->
            hsame germB globalB ->
              SheafBHistPointGermLedger point common sectA globalA ∧
                SheafBHistPointGermLedger point common sectB globalB ∧
                  hsame globalA globalB := by
  intro comparison globalACont globalBCont sameGlobalA sameGlobalB
  have ledgerA : SheafBHistPointGermLedger point common sectA globalA :=
    And.intro comparison.left
      (And.intro comparison.right.right.right.left globalACont)
  have ledgerB : SheafBHistPointGermLedger point common sectB globalB :=
    And.intro comparison.left
      (And.intro comparison.right.right.right.left globalBCont)
  have sameGlobal : hsame globalA globalB :=
    hsame_trans (hsame_symm sameGlobalA)
      (hsame_trans comparison.right.right.right.right.right.right.right.right sameGlobalB)
  exact And.intro ledgerA (And.intro ledgerB sameGlobal)

end BEDC.Derived.SheafUp
