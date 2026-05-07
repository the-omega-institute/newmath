import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SheafRestrictedCommonRefinement_pullback_compatibility
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB ->
          hsame openHist restrictedOpen ->
            Cont restrictedOpen sectionA restrictedGermA ->
              Cont restrictedOpen sectionB restrictedGermB ->
                Cont restrictedOpen sectionA globalA ->
                  Cont restrictedOpen sectionB globalB ->
                    SheafBHistPointGermComparison point restrictedOpen sectionA globalA
                        restrictedOpen sectionB globalB restrictedOpen ∧
                      hsame globalA globalB := by
  intro ledgerA ledgerB sameGerm sameOpen _restrictedA _restrictedB globalRowA globalRowB
  have readbackA :
      SheafBHistPointGermLedger point restrictedOpen sectionA globalA ∧
        hsame germA globalA :=
    SheafBHistPointGermLedger_restriction_readback ledgerA sameOpen globalRowA
  have readbackB :
      SheafBHistPointGermLedger point restrictedOpen sectionB globalB ∧
        hsame germB globalB :=
    SheafBHistPointGermLedger_restriction_readback ledgerB sameOpen globalRowB
  have sameGlobal : hsame globalA globalB :=
    hsame_trans (hsame_symm readbackA.right)
      (hsame_trans sameGerm readbackB.right)
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA globalA restrictedOpen
        sectionB globalB restrictedOpen :=
    (SheafBHistPointGermLedger_common_open_comparison
      readbackA.left readbackB.left sameGlobal).left
  exact And.intro comparison sameGlobal

theorem SheafRestrictedCommonRefinement_gluing_invariance
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              Cont restrictedOpen sectionA globalA ->
                Cont restrictedOpen sectionB globalB ->
                  SemanticNameCert
                    (fun endpoint : BHist =>
                      SheafBHistPointGermComparison point restrictedOpen sectionA globalA
                        restrictedOpen sectionB endpoint restrictedOpen)
                    (fun endpoint : BHist =>
                      SheafBHistPointGermComparison point restrictedOpen sectionA globalA
                        restrictedOpen sectionB endpoint restrictedOpen)
                    (fun endpoint : BHist =>
                      SheafBHistPointGermComparison point restrictedOpen sectionA globalA
                        restrictedOpen sectionB endpoint restrictedOpen)
                    hsame := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB globalRowA globalRowB
  have compatible :
      SheafBHistPointGermComparison point restrictedOpen sectionA globalA
          restrictedOpen sectionB globalB restrictedOpen ∧
        hsame globalA globalB :=
    SheafRestrictedCommonRefinement_pullback_compatibility
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB globalRowA globalRowB
  constructor
  · constructor
    · exact Exists.intro globalB compatible.left
    · intro endpoint _carrier
      exact hsame_refl endpoint
    · intro _endpoint _endpoint' same
      exact hsame_symm same
    · intro _endpoint _endpoint' _endpoint'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro endpoint endpoint' same carrier
      exact ⟨carrier.left, carrier.right.left, carrier.right.right.left,
        carrier.right.right.right.left, carrier.right.right.right.right.left,
        carrier.right.right.right.right.right.left,
        carrier.right.right.right.right.right.right.left,
        cont_result_hsame_transport carrier.right.right.right.right.right.right.right.left same,
        hsame_trans carrier.right.right.right.right.right.right.right.right same⟩
  · intro _endpoint source
    exact source
  · intro _endpoint source
    exact source

end BEDC.Derived.SheafUp
