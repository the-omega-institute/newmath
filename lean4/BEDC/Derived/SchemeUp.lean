import BEDC.Derived.RingedSpaceUp

namespace BEDC.Derived.SchemeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.CommRingUp
open BEDC.Derived.RingedSpaceUp
open BEDC.Derived.SheafUp

theorem SchemeAffineCoverLedger_restricted_global_soundness
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB ringEndpoint operationA operationB : BHist} :
    RingedSpaceSingletonSurface point openHist sectionA germA ringEndpoint ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              Cont restrictedOpen sectionA globalA ->
                Cont restrictedOpen sectionB globalB ->
                  CommRingSingletonClassifier operationA operationB ->
                    hsame globalA globalB ∧
                      CommRingSingletonClassifier operationA operationB ∧
                        RingedSpaceSingletonSurface point openHist sectionA germA
                          ringEndpoint := by
  intro surface ledgerB sameGerm sameOpen restrictedA restrictedB globalACont globalBCont
    commOps
  have sameGlobal :
      hsame globalA globalB :=
    SheafBHistPointGermComparison_restricted_global_soundness
      surface.right.left ledgerB sameGerm sameOpen restrictedA restrictedB globalACont globalBCont
      (cont_deterministic restrictedA globalACont) (cont_deterministic restrictedB globalBCont)
  exact And.intro sameGlobal (And.intro commOps surface)

end BEDC.Derived.SchemeUp
