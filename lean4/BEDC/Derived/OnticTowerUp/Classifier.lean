import BEDC.Derived.OnticTowerUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.OnticTowerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def OnticTowerClassifier
    (O A S R B L H C P N O' A' S' R' B' L' H' C' P' N' : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont
  hsame O O' ∧ hsame A A' ∧ hsame S S' ∧ hsame R R' ∧ hsame B B' ∧
    hsame L L' ∧ hsame H H' ∧ hsame C C' ∧ hsame P P' ∧ hsame N N' ∧
    hsame L (append A S)

theorem OnticTower_namecert_obligation_surface
    {O A S R B L H C P N O' A' S' R' B' L' H' C' P' N' : BHist} :
    OnticTowerClassifier O A S R B L H C P N O' A' S' R' B' L' H' C' P' N' →
      onticTowerFields (OnticTowerUp.mk O A S R B L H C P N) =
          [O, A, S, R, B, L, H, C, P, N] ∧
        hsame O O' ∧ hsame A A' ∧ hsame S S' ∧ hsame R R' ∧ hsame B B' ∧
        hsame L L' ∧ hsame H H' ∧ hsame C C' ∧ hsame P P' ∧ hsame N N' ∧
        hsame L (append A S) := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro classifier
  obtain
    ⟨sameO, sameA, sameS, sameR, sameB, sameL, sameH, sameC, sameP, sameN,
      sameAppend⟩ := classifier
  exact
    ⟨rfl, sameO, sameA, sameS, sameR, sameB, sameL, sameH, sameC, sameP, sameN,
      sameAppend⟩

end BEDC.Derived.OnticTowerUp
