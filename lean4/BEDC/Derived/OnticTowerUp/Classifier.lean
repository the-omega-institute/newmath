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

theorem OnticTower_observer_budget_separation
    {O A S R B L H C P N B' observerRead observerRead' : BHist} :
    Cont B C observerRead ->
      Cont B' C observerRead' ->
        (B ≠ B' ∨ observerRead ≠ observerRead') ->
          onticTowerFields (OnticTowerUp.mk O A S R B L H C P N) ≠
              onticTowerFields (OnticTowerUp.mk O A S R B' L H C P N) ∨
            observerRead ≠ observerRead' := by
  -- BEDC touchpoint anchor: BHist Cont
  intro _observerRoute _observerRoute' separated
  cases separated with
  | inl budgetSeparated =>
      left
      intro sameFields
      injection sameFields with _sameO tail1
      injection tail1 with _sameA tail2
      injection tail2 with _sameS tail3
      injection tail3 with _sameR tail4
      injection tail4 with sameBudget _tail5
      exact budgetSeparated sameBudget
  | inr readSeparated =>
      right
      exact readSeparated

end BEDC.Derived.OnticTowerUp
