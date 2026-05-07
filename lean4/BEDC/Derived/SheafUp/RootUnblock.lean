import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafRootUnblock_locality_gluing_faces
    {point openHist sectionA sectionB germA germB restrictedOpen restrictedGermA
      restrictedGermB globalA globalB : BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        hsame germA germB -> hsame openHist restrictedOpen ->
          Cont restrictedOpen sectionA restrictedGermA ->
            Cont restrictedOpen sectionB restrictedGermB ->
              Cont restrictedOpen sectionA globalA -> Cont restrictedOpen sectionB globalB ->
                SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
                  SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
                    SheafBHistPointGermComparison point restrictedOpen sectionA globalA
                      restrictedOpen sectionB globalB restrictedOpen ∧
                      SheafRootFaceRead restrictedOpen globalA .localityGluingRefinement ∧
                        hsame globalA globalB := by
  intro ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB globalACont globalBCont
  have descent :
      SheafBHistPointGermLedger point restrictedOpen sectionA restrictedGermA ∧
        SheafBHistPointGermLedger point restrictedOpen sectionB restrictedGermB ∧
          hsame restrictedGermA restrictedGermB :=
    SheafRestrictedOpenCarrier_locality_gluing_descent
      ledgerA ledgerB sameGerm sameOpen restrictedA restrictedB
  have sameGlobalA : hsame restrictedGermA globalA :=
    cont_deterministic restrictedA globalACont
  have sameGlobalB : hsame restrictedGermB globalB :=
    cont_deterministic restrictedB globalBCont
  have sameGlobal : hsame globalA globalB :=
    hsame_trans (hsame_symm sameGlobalA)
      (hsame_trans descent.right.right sameGlobalB)
  have comparison :
      SheafBHistPointGermComparison point restrictedOpen sectionA globalA
        restrictedOpen sectionB globalB restrictedOpen :=
    (SheafBHistPointGermLedger_common_open_comparison
      (And.intro descent.left.left (And.intro descent.left.right.left globalACont))
      (And.intro descent.right.left.left (And.intro descent.right.left.right.left globalBCont))
      sameGlobal).left
  have face :
      SheafRootFaceRead restrictedOpen globalA .localityGluingRefinement :=
    SheafRootFaceRead.localityGluingRefinement globalACont globalBCont sameGlobal
  exact And.intro descent.left
    (And.intro descent.right.left
      (And.intro comparison
        (And.intro face sameGlobal)))

end BEDC.Derived.SheafUp
