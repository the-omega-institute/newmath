import BEDC.Derived.SheafUp
import BEDC.FKernel.Cont.Cancellation

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

theorem SheafBHistPointGermLedger_hsame_transport_readback
    {point point' openHist openHist' sect sect' germ germ' : BHist} :
    SheafBHistPointGermLedger point openHist sect germ ->
      hsame point point' -> hsame openHist openHist' -> hsame sect sect' ->
        hsame germ germ' ->
          SheafBHistPointGermLedger point' openHist' sect' germ' ∧ UnaryHistory point' ∧
            UnaryHistory openHist' ∧ Cont openHist' sect' germ' := by
  intro ledger samePoint sameOpen sameSect sameGerm
  have pointUnary : UnaryHistory point' :=
    unary_transport ledger.left samePoint
  have openUnary : UnaryHistory openHist' :=
    unary_transport ledger.right.left sameOpen
  have transportedCont : Cont openHist' sect' germ' :=
    cont_hsame_transport sameOpen sameSect sameGerm ledger.right.right
  exact And.intro
    (And.intro pointUnary (And.intro openUnary transportedCont))
    (And.intro pointUnary (And.intro openUnary transportedCont))

theorem SheafBHistPointGermLedger_refinement_pullback_composition
    {point openU openV openW sect germU germV germW directGerm : BHist} :
    SheafBHistPointGermLedger point openU sect germU ->
      hsame openU openV -> Cont openV sect germV -> hsame openV openW ->
        Cont openW sect germW -> Cont openW sect directGerm ->
          SheafBHistPointGermLedger point openW sect directGerm ∧
            hsame germU directGerm ∧ hsame germV germW := by
  intro ledger sameUV rowV sameVW rowW directRow
  have readbackV :
      SheafBHistPointGermLedger point openV sect germV ∧ hsame germU germV :=
    SheafBHistPointGermLedger_restriction_readback ledger sameUV rowV
  have readbackW :
      SheafBHistPointGermLedger point openW sect germW ∧ hsame germV germW :=
    SheafBHistPointGermLedger_restriction_readback readbackV.left sameVW rowW
  have directLedger : SheafBHistPointGermLedger point openW sect directGerm :=
    And.intro readbackW.left.left (And.intro readbackW.left.right.left directRow)
  have sameWDirect : hsame germW directGerm :=
    cont_deterministic rowW directRow
  exact And.intro directLedger
    (And.intro
      (hsame_trans readbackV.right (hsame_trans readbackW.right sameWDirect))
      readbackW.right)

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
