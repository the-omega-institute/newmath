import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SheafRefinementGluing_descent_cont
    {point openA openB sectionA germA refinedGerm globalA globalRefined : BHist} :
    SheafBHistPointGermLedger point openA sectionA germA -> hsame openA openB ->
      Cont openB sectionA refinedGerm -> Cont openA sectionA globalA ->
        Cont openB sectionA globalRefined -> hsame germA globalA ->
          SheafBHistPointGermLedger point openB sectionA refinedGerm ∧
            hsame refinedGerm globalRefined ∧ hsame globalA globalRefined := by
  intro ledger sameOpen refinedRow _globalARow globalRefinedRow sameGermGlobalA
  have readback :
      SheafBHistPointGermLedger point openB sectionA refinedGerm ∧
        hsame germA refinedGerm :=
    SheafBHistPointGermLedger_restriction_readback ledger sameOpen refinedRow
  have sameRefinedGlobalRefined : hsame refinedGerm globalRefined :=
    cont_deterministic refinedRow globalRefinedRow
  have sameGlobalAGlobalRefined : hsame globalA globalRefined :=
    hsame_trans (hsame_symm sameGermGlobalA)
      (hsame_trans readback.right sameRefinedGlobalRefined)
  exact And.intro readback.left
    (And.intro sameRefinedGlobalRefined sameGlobalAGlobalRefined)

theorem SheafRefinedCover_gluing_uniqueness
    {point openHist sectionA sectionB localGerm globalA globalB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA globalA ->
      SheafBHistPointGermLedger point openHist sectionB globalB ->
        Cont openHist sectionA localGerm -> Cont openHist sectionB localGerm ->
          SheafBHistPointGermComparison point openHist sectionA localGerm openHist
              sectionB localGerm openHist ∧
            hsame globalA globalB := by
  intro ledgerA ledgerB localA localB
  have localLedgerA :
      SheafBHistPointGermLedger point openHist sectionA localGerm :=
    And.intro ledgerA.left (And.intro ledgerA.right.left localA)
  have localLedgerB :
      SheafBHistPointGermLedger point openHist sectionB localGerm :=
    And.intro ledgerB.left (And.intro ledgerB.right.left localB)
  have comparison :
      SheafBHistPointGermComparison point openHist sectionA localGerm openHist sectionB
        localGerm openHist ∧
        Cont openHist sectionA localGerm ∧ Cont openHist sectionB localGerm :=
    SheafBHistPointGermLedger_common_open_comparison
      localLedgerA localLedgerB (hsame_refl localGerm)
  have sameGlobalLocalA : hsame globalA localGerm :=
    cont_deterministic ledgerA.right.right localA
  have sameGlobalLocalB : hsame globalB localGerm :=
    cont_deterministic ledgerB.right.right localB
  exact And.intro comparison.left
    (hsame_trans sameGlobalLocalA (hsame_symm sameGlobalLocalB))

end BEDC.Derived.SheafUp
