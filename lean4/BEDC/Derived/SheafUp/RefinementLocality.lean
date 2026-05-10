import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafRefinementLocality_global_detection
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              Cont restrictedOpen sectionA globalA ->
                Cont restrictedOpen sectionB globalB ->
                  SheafBHistPointGermComparison point restrictedOpen sectionA globalA
                    restrictedOpen sectionB globalB restrictedOpen ∧ hsame globalA globalB := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB globalACont globalBCont
  have restrictedComparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA restrictedGermA
        restrictedOpen sectionB restrictedGermB restrictedOpen :=
    SheafBHistPointGermComparison_restricted_open_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have exactness :
      SheafBHistPointGermComparison point restrictedOpen sectionA globalA restrictedOpen
        sectionB globalB restrictedOpen ∧ hsame globalA globalB :=
    SheafRootCoverDescent_common_refinement_germ_exactness
      restrictedComparison globalACont globalBCont
      (cont_deterministic restrictedA globalACont)
      (cont_deterministic restrictedB globalBCont)
  exact exactness

end BEDC.Derived.SheafUp
