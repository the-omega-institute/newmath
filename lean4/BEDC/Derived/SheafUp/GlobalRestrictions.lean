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

theorem SheafGluingGlobalRestrictions_idempotent
    {point openHist sectionG sectionH globalG globalH localG localH : BHist} :
    SheafBHistPointGermLedger point openHist sectionG globalG ->
      SheafBHistPointGermLedger point openHist sectionH globalH ->
        Cont openHist sectionG localG ->
          Cont openHist sectionH localH ->
            hsame localH localG ->
              hsame globalH globalG ∧
                SheafBHistPointGermComparison point openHist sectionH localH openHist
                  sectionG localG openHist := by
  intro ledgerG ledgerH localRowG localRowH sameLocals
  have sameGlobalLocalG : hsame globalG localG :=
    cont_deterministic ledgerG.right.right localRowG
  have sameGlobalLocalH : hsame globalH localH :=
    cont_deterministic ledgerH.right.right localRowH
  have sameGlobals : hsame globalH globalG :=
    hsame_trans sameGlobalLocalH
      (hsame_trans sameLocals (hsame_symm sameGlobalLocalG))
  have localLedgerG :
      SheafBHistPointGermLedger point openHist sectionG localG :=
    And.intro ledgerG.left (And.intro ledgerG.right.left localRowG)
  have localLedgerH :
      SheafBHistPointGermLedger point openHist sectionH localH :=
    And.intro ledgerH.left (And.intro ledgerH.right.left localRowH)
  have comparison :=
    SheafBHistPointGermLedger_common_open_comparison localLedgerH localLedgerG sameLocals
  exact And.intro sameGlobals comparison.left

end BEDC.Derived.SheafUp
