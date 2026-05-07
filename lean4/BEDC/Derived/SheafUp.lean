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
