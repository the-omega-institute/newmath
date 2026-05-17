import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LocalClockBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

inductive LocalClockBudgetUp : Type where
  | mk : (H T W B L Q P N : BHist) → LocalClockBudgetUp

def localClockBudgetFields : LocalClockBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist hsame Cont
  | LocalClockBudgetUp.mk H T W B L Q P N => [H, T, W, B, L, Q, P, N]

def LocalClockBudgetCarrier (H T W B L Q P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont
  hsame H H ∧ hsame T T ∧ hsame W W ∧ hsame B B ∧ hsame L L ∧ hsame Q Q ∧
    hsame P P ∧ hsame N N ∧
      localClockBudgetFields (LocalClockBudgetUp.mk H T W B L Q P N) =
        [H, T, W, B, L, Q, P, N]

def LocalClockBudgetWindowSurface (H T W B Q : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont
  Cont BHist.Empty T H ∧ Cont T W Q ∧ hsame B B

theorem LocalClockBudgetWindow_totality {H T W B L Q P N : BHist} :
    LocalClockBudgetCarrier H T W B L Q P N →
      Cont BHist.Empty T H →
        Cont T W Q →
          LocalClockBudgetWindowSurface H T W B Q ∧
            localClockBudgetFields (LocalClockBudgetUp.mk H T W B L Q P N) =
              [H, T, W, B, L, Q, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro carrier streamRoute windowRoute
  constructor
  · constructor
    · exact streamRoute
    · constructor
      · exact windowRoute
      · rfl
  · exact carrier.right.right.right.right.right.right.right.right

theorem LocalClockBudgetClassifier_stability
    {H T W B L Q P N H' T' W' B' Q' P' N' : BHist}
    (carrier : LocalClockBudgetCarrier H T W B L Q P N)
    (streamRoute : Cont BHist.Empty T H)
    (windowRoute : Cont T W Q)
    (hH : hsame H H')
    (hT : hsame T T')
    (hW : hsame W W')
    (hB : hsame B B')
    (hQ : hsame Q Q')
    (hP : hsame P P')
    (hN : hsame N N') :
    LocalClockBudgetWindowSurface H T W B Q ∧
      hsame H H' ∧
        hsame T T' ∧
          hsame W W' ∧
            hsame B B' ∧
              hsame Q Q' ∧
                hsame P P' ∧
                  hsame N N' ∧
                    localClockBudgetFields (LocalClockBudgetUp.mk H T W B L Q P N) =
                      [H, T, W, B, L, Q, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  have total := LocalClockBudgetWindow_totality carrier streamRoute windowRoute
  constructor
  · exact total.left
  · constructor
    · exact hH
    · constructor
      · exact hT
      · constructor
        · exact hW
        · constructor
          · exact hB
          · constructor
            · exact hQ
            · constructor
              · exact hP
              · constructor
                · exact hN
                · exact total.right

theorem LocalClockBudgetRoute_determinacy
    {H T W B L Q P N H' T' W' B' L' Q' P' N' : BHist}
    (left : LocalClockBudgetCarrier H T W B L Q P N)
    (right : LocalClockBudgetCarrier H' T' W' B' L' Q' P' N')
    (stream : Cont BHist.Empty T H)
    (stream' : Cont BHist.Empty T' H')
    (window : Cont T W Q)
    (window' : Cont T' W' Q')
    (sameH : hsame H H')
    (sameT : hsame T T')
    (sameW : hsame W W')
    (sameB : hsame B B')
    (sameL : hsame L L')
    (sameQ : hsame Q Q')
    (sameP : hsame P P')
    (sameN : hsame N N') :
    LocalClockBudgetWindowSurface H T W B Q ∧
      LocalClockBudgetWindowSurface H' T' W' B' Q' ∧
        hsame Q Q' ∧
          localClockBudgetFields (LocalClockBudgetUp.mk H T W B L Q P N) =
            localClockBudgetFields (LocalClockBudgetUp.mk H' T' W' B' L' Q' P' N') := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  have leftSurface :=
    (LocalClockBudgetWindow_totality left stream window).left
  have rightSurface :=
    (LocalClockBudgetWindow_totality right stream' window').left
  constructor
  · exact leftSurface
  · constructor
    · exact rightSurface
    · constructor
      · exact sameQ
      · cases sameH
        cases sameT
        cases sameW
        cases sameB
        cases sameL
        cases sameQ
        cases sameP
        cases sameN
        rfl

theorem LocalClockBudgetCarrier_observer_handoff
    {H T W B L Q P N observerRead : BHist}
    (carrier : LocalClockBudgetCarrier H T W B L Q P N)
    (streamRoute : Cont BHist.Empty T H)
    (windowRoute : Cont T W Q)
    (observerRoute : Cont Q P observerRead) :
    LocalClockBudgetWindowSurface H T W B Q ∧
      Cont Q P observerRead ∧
        hsame H H ∧
          hsame N N ∧
            localClockBudgetFields (LocalClockBudgetUp.mk H T W B L Q P N) =
              [H, T, W, B, L, Q, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  have total := LocalClockBudgetWindow_totality carrier streamRoute windowRoute
  exact
    ⟨total.left, observerRoute, hsame_refl H, hsame_refl N, total.right⟩

theorem LocalClockBudgetCarrier_scope {H T W B L Q P N : BHist}
    (carrier : LocalClockBudgetCarrier H T W B L Q P N)
    (streamRoute : Cont BHist.Empty T H)
    (windowRoute : Cont T W Q) :
    LocalClockBudgetWindowSurface H T W B Q ∧
      hsame H H ∧
        hsame T T ∧
          hsame W W ∧
            hsame B B ∧
              hsame L L ∧
                hsame Q Q ∧
                  hsame P P ∧
                    hsame N N ∧
                      localClockBudgetFields (LocalClockBudgetUp.mk H T W B L Q P N) =
                        [H, T, W, B, L, Q, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  have total := LocalClockBudgetWindow_totality carrier streamRoute windowRoute
  exact
    ⟨total.left, hsame_refl H, hsame_refl T, hsame_refl W, hsame_refl B,
      hsame_refl L, hsame_refl Q, hsame_refl P, hsame_refl N, total.right⟩

theorem LocalClockBudgetLedger_boundary
    {H T W B L Q P N ledgerRead handoffRead : BHist}
    (carrier : LocalClockBudgetCarrier H T W B L Q P N)
    (streamRoute : Cont BHist.Empty T H)
    (windowRoute : Cont T W Q)
    (ledgerRoute : Cont L Q ledgerRead)
    (handoffRoute : Cont ledgerRead N handoffRead) :
    LocalClockBudgetWindowSurface H T W B Q ∧
      Cont L Q ledgerRead ∧
        Cont ledgerRead N handoffRead ∧
          hsame L L ∧
            hsame N N ∧
              localClockBudgetFields (LocalClockBudgetUp.mk H T W B L Q P N) =
                [H, T, W, B, L, Q, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  have total := LocalClockBudgetWindow_totality carrier streamRoute windowRoute
  constructor
  · exact total.left
  · constructor
    · exact ledgerRoute
    · constructor
      · exact handoffRoute
      · constructor
        · rfl
        · constructor
          · rfl
          · exact total.right

theorem LocalClockBudgetNameCert_obligations {H T W B L Q P N : BHist}
    (carrier : LocalClockBudgetCarrier H T W B L Q P N)
    (streamRoute : Cont BHist.Empty T H)
    (windowRoute : Cont T W Q) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row H ∧
          localClockBudgetFields (LocalClockBudgetUp.mk H T W B L Q P N) =
            [H, T, W, B, L, Q, P, N])
      (fun row : BHist => hsame row H ∧ hsame T T ∧ hsame W W ∧ hsame B B)
      (fun row : BHist =>
        Cont BHist.Empty T H ∧ Cont T W Q ∧ hsame row H ∧ hsame L L ∧
          hsame P P ∧ hsame N N)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont SemanticNameCert hsame
  have fields :
      localClockBudgetFields (LocalClockBudgetUp.mk H T W B L Q P N) =
        [H, T, W, B, L, Q, P, N] :=
    carrier.right.right.right.right.right.right.right.right
  exact {
    core := {
      carrier_inhabited := Exists.intro H ⟨hsame_refl H, fields⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, hsame_refl T, hsame_refl W, hsame_refl B⟩
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨streamRoute, windowRoute, sourceRow.left, hsame_refl L, hsame_refl P,
          hsame_refl N⟩
  }

end BEDC.Derived.LocalClockBudgetUp
