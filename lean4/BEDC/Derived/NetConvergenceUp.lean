import BEDC.Derived.NetConvergenceUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NetConvergenceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def NetConvergenceCarrier (D T E A F S R L H C P M : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame Cont
  hsame D D ∧ hsame T T ∧ hsame E E ∧ hsame A A ∧ hsame F F ∧ hsame S S ∧
    hsame R R ∧ hsame L L ∧ hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame M M ∧
      netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
        [D, T, E, A, F, S, R, L, H, C, P, M]

theorem NetConvergenceNameCert_obligations {D T E A F S R L H C P M : BHist}
    (carrier : NetConvergenceCarrier D T E A F S R L H C P M)
    (tailRoute : Cont D T E)
    (filterRoute : Cont E F S)
    (realRoute : Cont S R L) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row D ∧
          netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
            [D, T, E, A, F, S, R, L, H, C, P, M])
      (fun row : BHist => hsame row D ∧ Cont D T E ∧ Cont E F S)
      (fun row : BHist =>
        Cont S R L ∧ hsame row D ∧ hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame M M)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have fields :
      netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
        [D, T, E, A, F, S, R, L, H, C, P, M] :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  exact {
    core := {
      carrier_inhabited := Exists.intro D ⟨hsame_refl D, fields⟩
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
      exact ⟨sourceRow.left, tailRoute, filterRoute⟩
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨realRoute, sourceRow.left, hsame_refl H, hsame_refl C, hsame_refl P,
          hsame_refl M⟩
  }

theorem NetConvergenceCarrier_cauchy_filter_handoff {D T E A F S R L H C P M
    handoffRead realRead : BHist}
    (carrier : NetConvergenceCarrier D T E A F S R L H C P M)
    (tailRoute : Cont D T E)
    (filterRoute : Cont E F S)
    (realRoute : Cont S R L)
    (handoffSame : hsame handoffRead D)
    (realSame : hsame realRead D) :
    (Cont D T E ∧ Cont E F S ∧ hsame handoffRead D) ∧
      (Cont S R L ∧ hsame realRead D ∧ hsame H H ∧ hsame C C ∧ hsame P P ∧
        hsame M M ∧
        netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
          [D, T, E, A, F, S, R, L, H, C, P, M]) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have fields :
      netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
        [D, T, E, A, F, S, R, L, H, C, P, M] :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row D ∧
            netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
              [D, T, E, A, F, S, R, L, H, C, P, M])
        (fun row : BHist => hsame row D ∧ Cont D T E ∧ Cont E F S)
        (fun row : BHist =>
          Cont S R L ∧ hsame row D ∧ hsame H H ∧ hsame C C ∧ hsame P P ∧
            hsame M M)
        hsame :=
    NetConvergenceNameCert_obligations carrier tailRoute filterRoute realRoute
  have handoffPattern : hsame handoffRead D ∧ Cont D T E ∧ Cont E F S :=
    cert.pattern_sound ⟨handoffSame, fields⟩
  have realLedger :
      Cont S R L ∧ hsame realRead D ∧ hsame H H ∧ hsame C C ∧ hsame P P ∧
        hsame M M :=
    cert.ledger_sound ⟨realSame, fields⟩
  exact
    ⟨⟨handoffPattern.right.left, handoffPattern.right.right, handoffPattern.left⟩,
      ⟨realLedger.left, realLedger.right.left, realLedger.right.right.left,
        realLedger.right.right.right.left, realLedger.right.right.right.right.left,
        realLedger.right.right.right.right.right, fields⟩⟩

end BEDC.Derived.NetConvergenceUp
