import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafBHistPointGermLedger_global_restrictions_compatible
    {point openHist sectionA sectionB globalA globalB localA localB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA globalA ->
      SheafBHistPointGermLedger point openHist sectionB globalB ->
        Cont openHist sectionA localA ->
          Cont openHist sectionB localB ->
            hsame globalA globalB ->
              SheafBHistPointGermComparison point openHist sectionA localA openHist sectionB
                  localB openHist ∧
                hsame localA localB := by
  intro ledgerA ledgerB localRowA localRowB sameGlobals
  have sameGlobalLocalA : hsame globalA localA :=
    cont_deterministic ledgerA.right.right localRowA
  have sameGlobalLocalB : hsame globalB localB :=
    cont_deterministic ledgerB.right.right localRowB
  have sameLocals : hsame localA localB :=
    hsame_trans (hsame_symm sameGlobalLocalA)
      (hsame_trans sameGlobals sameGlobalLocalB)
  have localLedgerA :
      SheafBHistPointGermLedger point openHist sectionA localA :=
    And.intro ledgerA.left (And.intro ledgerA.right.left localRowA)
  have localLedgerB :
      SheafBHistPointGermLedger point openHist sectionB localB :=
    And.intro ledgerB.left (And.intro ledgerB.right.left localRowB)
  have comparison :=
    SheafBHistPointGermLedger_common_open_comparison localLedgerA localLedgerB sameLocals
  exact And.intro comparison.left sameLocals

end BEDC.Derived.SheafUp
