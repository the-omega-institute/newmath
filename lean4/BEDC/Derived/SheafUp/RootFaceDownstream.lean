import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafRootFaceRead_downstream_separation
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB chartEndpoint : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB ->
          hsame openHist restrictedOpen ->
            Cont restrictedOpen sectionA restrictedGermA ->
              Cont restrictedOpen sectionB restrictedGermB ->
                hsame chartEndpoint restrictedGermB ->
                  SheafRootFaceRead restrictedOpen restrictedGermA .restrictionRoute ∧
                    SheafRootFaceRead restrictedOpen restrictedGermB .restrictionRoute ∧
                      SheafRootFaceRead restrictedOpen restrictedGermA
                        .localityGluingRefinement ∧
                        hsame chartEndpoint restrictedGermB := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB sameChart
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  exact And.intro (SheafRootFaceRead.restrictionRoute restrictedA)
    (And.intro (SheafRootFaceRead.restrictionRoute restrictedB)
      (And.intro
        (SheafRootFaceRead.localityGluingRefinement
          descent.left.right.right descent.right.left.right.right descent.right.right)
        sameChart))

end BEDC.Derived.SheafUp
