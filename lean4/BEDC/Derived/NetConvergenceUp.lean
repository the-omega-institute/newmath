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

theorem NetConvergenceCarrier_moore_smith_dependency
    {D T E A F S R L H C P M sourceRead filterRead realRead : BHist} :
    NetConvergenceCarrier D T E A F S R L H C P M ->
      Cont D A sourceRead ->
        Cont sourceRead F filterRead ->
          Cont filterRead L realRead ->
            hsame D D ∧ hsame A A ∧ hsame F F ∧ hsame L L ∧
              Cont D A sourceRead ∧ Cont sourceRead F filterRead ∧
                Cont filterRead L realRead ∧
                  netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
                    [D, T, E, A, F, S, R, L, H, C, P, M] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro carrier sourceRoute filterRoute realRoute
  obtain ⟨sameD, _sameT, _sameE, sameA, sameF, _sameS, _sameR, sameL, _sameH,
    _sameC, _sameP, _sameM, fields⟩ := carrier
  exact
    ⟨sameD, sameA, sameF, sameL, sourceRoute, filterRoute, realRoute, fields⟩

theorem NetConvergenceCarrier_directed_window_admission {D T E A F S R L H C P M
    read : BHist} :
    NetConvergenceCarrier D T E A F S R L H C P M ->
      Cont D T E ->
        hsame read D ->
          hsame D D ∧ hsame T T ∧ hsame E E ∧ Cont D T E ∧ hsame read D ∧
            netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
              [D, T, E, A, F, S, R, L, H, C, P, M] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro carrier directedWindow readSame
  obtain ⟨sameD, sameT, sameE, _sameA, _sameF, _sameS, _sameR, _sameL, _sameH,
    _sameC, _sameP, _sameM, fields⟩ := carrier
  exact ⟨sameD, sameT, sameE, directedWindow, readSame, fields⟩

theorem NetConvergenceCarrier_tail_window_admission {D T E A F S R L H C P M
    filterRead streamRead : BHist} :
    NetConvergenceCarrier D T E A F S R L H C P M ->
      Cont D T E ->
        Cont E F filterRead ->
          Cont filterRead S streamRead ->
            hsame streamRead D ->
              hsame D D ∧ hsame T T ∧ hsame E E ∧ hsame F F ∧ hsame S S ∧
                Cont D T E ∧ Cont E F filterRead ∧ Cont filterRead S streamRead ∧
                  hsame streamRead D ∧
                    netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
                      [D, T, E, A, F, S, R, L, H, C, P, M] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro carrier tailRoute filterRoute streamRoute streamSame
  obtain ⟨sameD, sameT, sameE, _sameA, sameF, sameS, _sameR, _sameL, _sameH,
    _sameC, _sameP, _sameM, fields⟩ := carrier
  exact
    ⟨sameD, sameT, sameE, sameF, sameS, tailRoute, filterRoute, streamRoute,
      streamSame, fields⟩

theorem NetConvergenceCarrier_filterbase_finality {D T E A F S R L H C P M
    filterbaseRead handoffRead : BHist}
    (carrier : NetConvergenceCarrier D T E A F S R L H C P M)
    (tailRoute : Cont D T E)
    (filterbaseRoute : Cont T E filterbaseRead)
    (handoffRoute : Cont E F handoffRead)
    (filterbaseSame : hsame filterbaseRead D)
    (handoffSame : hsame handoffRead F) :
    hsame D D ∧ hsame T T ∧ hsame E E ∧ hsame F F ∧ Cont D T E ∧
      Cont T E filterbaseRead ∧ Cont E F handoffRead ∧ hsame filterbaseRead D ∧
        hsame handoffRead F ∧
          netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
            [D, T, E, A, F, S, R, L, H, C, P, M] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  obtain ⟨sameD, sameT, sameE, _sameA, sameF, _sameS, _sameR, _sameL, _sameH,
    _sameC, _sameP, _sameM, fields⟩ := carrier
  exact
    ⟨sameD, sameT, sameE, sameF, tailRoute, filterbaseRoute, handoffRoute,
      filterbaseSame, handoffSame, fields⟩

theorem NetConvergenceCarrier_cauchy_net_limit_handoff
    {D T E A F S R L H C P M sourceRead limitRead : BHist}
    (carrier : NetConvergenceCarrier D T E A F S R L H C P M)
    (sourceRoute : Cont D A sourceRead)
    (limitRoute : Cont sourceRead L limitRead)
    (realRoute : Cont S R L)
    (limitSame : hsame limitRead D) :
    (Cont D A sourceRead ∧ Cont sourceRead L limitRead ∧ hsame limitRead D) ∧
      (Cont S R L ∧ hsame L L ∧
        netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
          [D, T, E, A, F, S, R, L, H, C, P, M]) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  obtain ⟨_sameD, _sameT, _sameE, _sameA, _sameF, _sameS, _sameR, sameL, _sameH,
    _sameC, _sameP, _sameM, fields⟩ := carrier
  exact ⟨⟨sourceRoute, limitRoute, limitSame⟩, ⟨realRoute, sameL, fields⟩⟩

theorem NetConvergenceCarrier_moore_smith_filter_boundary
    {D T E A F S R L H C P M sourceRead filterRead : BHist} :
    NetConvergenceCarrier D T E A F S R L H C P M →
      Cont D T E →
        Cont D A sourceRead →
          Cont E F filterRead →
            hsame sourceRead D →
              hsame filterRead D →
                Cont D T E ∧ Cont D A sourceRead ∧ Cont E F filterRead ∧
                  hsame sourceRead D ∧ hsame filterRead D ∧ hsame H H ∧ hsame C C ∧
                    hsame P P ∧ hsame M M ∧
                      netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
                        [D, T, E, A, F, S, R, L, H, C, P, M] := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro carrier directedTail sourceRoute filterRoute sourceSame filterSame
  obtain ⟨_sameD, _sameT, _sameE, _sameA, _sameF, _sameS, _sameR, _sameL, sameH,
    sameC, sameP, sameM, fields⟩ := carrier
  exact
    ⟨directedTail, sourceRoute, filterRoute, sourceSame, filterSame, sameH, sameC, sameP,
      sameM, fields⟩

theorem NetConvergenceCarrier_stream_readback_route
    {D T E A F S R L H C P M streamRead sealRead : BHist} :
    NetConvergenceCarrier D T E A F S R L H C P M ->
      Cont F S streamRead ->
        Cont streamRead R sealRead ->
          hsame sealRead D ->
            hsame F F ∧ hsame S S ∧ hsame R R ∧ hsame L L ∧
              Cont F S streamRead ∧ Cont streamRead R sealRead ∧ hsame sealRead D ∧
                netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
                  [D, T, E, A, F, S, R, L, H, C, P, M] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro carrier streamRoute sealRoute sealSame
  obtain ⟨_sameD, _sameT, _sameE, _sameA, sameF, sameS, sameR, sameL, _sameH,
    _sameC, _sameP, _sameM, fields⟩ := carrier
  exact
    ⟨sameF, sameS, sameR, sameL, streamRoute, sealRoute, sealSame, fields⟩

end BEDC.Derived.NetConvergenceUp
