import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem SheafRestrictedOpenCarrier_semantic_name_certificate
    {point openHist sectionHist germ : BHist} :
    SheafBHistPointGermLedger point openHist sectionHist germ ->
      SemanticNameCert
        (fun endpoint : BHist => SheafBHistPointGermLedger point openHist sectionHist endpoint)
        (fun endpoint : BHist => SheafBHistPointGermLedger point openHist sectionHist endpoint)
        (fun endpoint : BHist => SheafBHistPointGermLedger point openHist sectionHist endpoint)
        hsame := by
  intro ledger
  constructor
  · constructor
    · exact Exists.intro germ ledger
    · intro endpoint _carrier
      exact hsame_refl endpoint
    · intro endpoint endpoint' same
      exact hsame_symm same
    · intro endpoint endpoint' endpoint'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro endpoint endpoint' same carrier
      exact And.intro carrier.left
        (And.intro carrier.right.left
          (cont_result_hsame_transport carrier.right.right same))
  · intro _endpoint source
    exact source
  · intro _endpoint source
    exact source

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

theorem SheafBHistPointGermComparison_soundness
    {point openA openB sectA sectB germA germB common globalA globalB : BHist} :
    SheafBHistPointGermComparison point openA sectA germA openB sectB germB common ->
      Cont common sectA globalA -> Cont common sectB globalB ->
        hsame germA globalA -> hsame germB globalB -> hsame globalA globalB := by
  intro comparison _globalACont _globalBCont sameGlobalA sameGlobalB
  exact hsame_trans (hsame_symm sameGlobalA)
    (hsame_trans comparison.right.right.right.right.right.right.right.right sameGlobalB)

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

theorem SheafRestrictedOpenCarrier_locality_gluing_descent
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB ->
          hsame openHist restrictedOpen ->
            Cont restrictedOpen sectionA restrictedGermA ->
              Cont restrictedOpen sectionB restrictedGermB ->
                SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                  SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                    hsame restrictedGermA restrictedGermB := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have readbackA :=
    SheafBHistPointGermLedger_restriction_readback ledgerA sameOpen restrictedA
  have readbackB :=
    SheafBHistPointGermLedger_restriction_readback ledgerB sameOpen restrictedB
  have sameRestrictedA : hsame restrictedGermA germA := hsame_symm readbackA.right
  have sameRestrictedB : hsame germB restrictedGermB := readbackB.right
  exact And.intro readbackA.left
    (And.intro readbackB.left
      (hsame_trans sameRestrictedA (hsame_trans sameGerm sameRestrictedB)))

theorem SheafBHistPointGermComparison_restricted_open_descent
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
                restrictedOpen sectionB restrictedGermB restrictedOpen := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have comparison :=
    SheafBHistPointGermLedger_common_open_comparison
      descent.left descent.right.left descent.right.right
  exact comparison.left

theorem SheafBHistPointGermLedger_restricted_global_soundness
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              Cont restrictedOpen sectionA globalA -> Cont restrictedOpen sectionB globalB ->
                hsame restrictedGermA globalA ∧ hsame restrictedGermB globalB ∧
                  hsame globalA globalB := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB globalRowA globalRowB
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have sameGlobalA : hsame restrictedGermA globalA :=
    cont_deterministic restrictedA globalRowA
  have sameGlobalB : hsame restrictedGermB globalB :=
    cont_deterministic restrictedB globalRowB
  exact And.intro sameGlobalA
    (And.intro sameGlobalB
      (hsame_trans (hsame_symm sameGlobalA)
        (hsame_trans descent.right.right sameGlobalB)))

end BEDC.Derived.SheafUp
