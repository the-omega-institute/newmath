import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem SheafGluingClassifier_uniqueness_from_locality
    {point openHist sectionA sectionB localSection germA germB localGermA localGermB :
      BHist} :
    SheafBHistPointGermLedger point openHist sectionA germA ->
      SheafBHistPointGermLedger point openHist sectionB germB ->
        Cont openHist sectionA localGermA ->
          Cont openHist localSection localGermA ->
            Cont openHist sectionB localGermB ->
              Cont openHist localSection localGermB ->
                hsame germA germB ∧ hsame localGermA localGermB := by
  intro ledgerA ledgerB sectionARow localRowA sectionBRow localRowB
  have sameA : hsame germA localGermA :=
    cont_deterministic ledgerA.right.right sectionARow
  have sameB : hsame germB localGermB :=
    cont_deterministic ledgerB.right.right sectionBRow
  have sameLocal : hsame localGermA localGermB :=
    cont_deterministic localRowA localRowB
  exact And.intro
    (hsame_trans sameA (hsame_trans sameLocal (hsame_symm sameB)))
    sameLocal

end BEDC.Derived.SheafUp
