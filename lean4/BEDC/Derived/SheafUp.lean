import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafBHistPointGermLedger
    (point openHist sectionHist germ : BHist) : Prop :=
  UnaryHistory point ∧ UnaryHistory openHist ∧ Cont openHist sectionHist germ

def SheafBHistPointGermComparison
    (point openA sectA germA openB sectB germB common : BHist) : Prop :=
  UnaryHistory point ∧ UnaryHistory openA ∧ UnaryHistory openB ∧ UnaryHistory common ∧
    hsame common openA ∧ hsame common openB ∧ Cont common sectA germA ∧
      Cont common sectB germB ∧ hsame germA germB

theorem SheafBHistPointGermLedger_restriction_readback
    {point openHist sectionHist germ restrictedOpen restrictedGerm : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen sectionHist restrictedGerm ->
          SheafBHistPointGermLedger point restrictedOpen sectionHist restrictedGerm ∧
            hsame germ restrictedGerm := by
  intro ledger sameOpen restrictedRow
  cases sameOpen
  have restrictedOpenUnary : UnaryHistory openHist := ledger.right.left
  have sameGerm : hsame germ restrictedGerm :=
    cont_deterministic ledger.right.right restrictedRow
  exact And.intro
    (And.intro ledger.left (And.intro restrictedOpenUnary restrictedRow))
    sameGerm

theorem SheafRestrictedOpenCarrier_restriction_laws
    {point openHist sectionHist germ restrictedOpen restrictedGerm : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      hsame openHist restrictedOpen ->
        Cont restrictedOpen sectionHist restrictedGerm ->
          UnaryHistory point ∧ UnaryHistory restrictedOpen ∧
            Cont restrictedOpen sectionHist restrictedGerm ∧ hsame germ restrictedGerm := by
  intro ledger sameOpen restrictedRow
  cases sameOpen
  have sameGerm : hsame germ restrictedGerm :=
    cont_deterministic ledger.right.right restrictedRow
  exact And.intro ledger.left
    (And.intro ledger.right.left
      (And.intro restrictedRow sameGerm))

theorem SheafBHistPointGermLedger_gluing_readback
    {point openHist sect germ memberOpen memberSect memberGerm : BHist} :
    SheafBHistPointGermLedger point openHist sect germ ->
      UnaryHistory memberOpen -> hsame openHist memberOpen -> hsame sect memberSect ->
        Cont memberOpen memberSect memberGerm ->
          SheafBHistPointGermLedger point memberOpen memberSect memberGerm ∧
            hsame germ memberGerm := by
  intro ledger memberOpenUnary sameOpen sameSect memberRow
  cases sameOpen
  cases sameSect
  have sameGerm : hsame germ memberGerm :=
    cont_deterministic ledger.right.right memberRow
  exact And.intro
    (And.intro ledger.left (And.intro memberOpenUnary memberRow))
    sameGerm

theorem SheafBHistPointGermComparison_trans
    {point openA openB openC sectA sectB sectC germA germB germC common : BHist} :
    SheafBHistPointGermComparison point openA sectA germA openB sectB germB common ->
      SheafBHistPointGermComparison point openB sectB germB openC sectC germC common ->
        SheafBHistPointGermComparison point openA sectA germA openC sectC germC common := by
  intro first second
  exact And.intro first.left
    (And.intro first.right.left
      (And.intro second.right.right.left
        (And.intro first.right.right.right.left
          (And.intro first.right.right.right.right.left
            (And.intro second.right.right.right.right.right.left
              (And.intro first.right.right.right.right.right.right.left
                (And.intro second.right.right.right.right.right.right.right.left
                  (hsame_trans first.right.right.right.right.right.right.right.right
                    second.right.right.right.right.right.right.right.right))))))))

theorem SheafBHistPointGermComparison_symmetric_fields
    {point openA openB sectA sectB germA germB common : BHist} :
    SheafBHistPointGermComparison point openA sectA germA openB sectB germB common ->
      UnaryHistory point ∧ UnaryHistory openB ∧ UnaryHistory openA ∧ UnaryHistory common ∧
        hsame common openB ∧ hsame common openA ∧ Cont common sectB germB ∧
          Cont common sectA germA ∧ hsame germB germA := by
  intro comparison
  exact And.intro comparison.left
    (And.intro comparison.right.right.left
      (And.intro comparison.right.left
        (And.intro comparison.right.right.right.left
          (And.intro comparison.right.right.right.right.right.left
            (And.intro comparison.right.right.right.right.left
              (And.intro comparison.right.right.right.right.right.right.right.left
                (And.intro comparison.right.right.right.right.right.right.left
                  (hsame_symm comparison.right.right.right.right.right.right.right.right))))))))

theorem SheafBHistPointGermLedger_common_open_comparison
    {point openHist sectA sectB germA germB : BHist} :
    SheafBHistPointGermLedger point openHist sectA germA ->
      SheafBHistPointGermLedger point openHist sectB germB ->
        hsame germA germB ->
          SheafBHistPointGermComparison point openHist sectA germA openHist sectB germB
              openHist ∧
            Cont openHist sectA germA ∧ Cont openHist sectB germB := by
  intro ledgerA ledgerB sameGerm
  have openCommon : UnaryHistory openHist := ledgerA.right.left
  have comparison :
      SheafBHistPointGermComparison point openHist sectA germA openHist sectB germB
        openHist :=
    And.intro ledgerA.left
      (And.intro ledgerA.right.left
        (And.intro ledgerB.right.left
          (And.intro openCommon
            (And.intro (hsame_refl openHist)
              (And.intro (hsame_refl openHist)
                (And.intro ledgerA.right.right
                  (And.intro ledgerB.right.right sameGerm)))))))
  exact And.intro comparison (And.intro ledgerA.right.right ledgerB.right.right)

theorem SheafBHistPointGermLedger_shared_open_classifier_transitivity
    {point openA openB openC sectionA sectionB sectionC germA germB germC : BHist} :
    SheafBHistPointGermLedger point openA sectionA germA ->
      SheafBHistPointGermLedger point openB sectionB germA ->
        SheafBHistPointGermLedger point openB sectionB germB ->
          SheafBHistPointGermLedger point openC sectionC germB ->
            UnaryHistory sectionC -> Cont openA sectionC germC ->
              SheafBHistPointGermLedger point openA sectionC germC ∧
                hsame germA germB ∧ UnaryHistory germC := by
  intro rowA sharedA sharedB _rowC sectionCUnary directAC
  have sameAB : hsame germA germB :=
    cont_deterministic sharedA.right.right sharedB.right.right
  have germCUnary : UnaryHistory germC :=
    unary_cont_closed rowA.right.left sectionCUnary directAC
  exact And.intro
    (And.intro rowA.left (And.intro rowA.right.left directAC))
    (And.intro sameAB germCUnary)

end BEDC.Derived.SheafUp
