import BEDC.Derived.NetConvergenceUp

namespace BEDC.Derived.NetConvergenceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem NetConvergenceCarrier_real_seal_nonescape
    {D T E A F S R L H C P M filterRead streamRead sealRead : BHist} :
    NetConvergenceCarrier D T E A F S R L H C P M →
      Cont D T E →
        Cont E F filterRead →
          Cont F S streamRead →
            Cont streamRead R sealRead →
              hsame sealRead L →
                Cont D T E ∧ Cont E F filterRead ∧ Cont F S streamRead ∧
                  Cont streamRead R sealRead ∧ hsame sealRead L ∧ hsame L L ∧
                    netConvergenceFields (NetConvergenceUp.mk D T E A F S R L H C P M) =
                      [D, T, E, A, F, S, R, L, H, C, P, M] := by
  -- BEDC touchpoint anchor: BHist hsame Cont
  intro carrier directedRoute filterRoute streamRoute sealRoute sealSame
  obtain ⟨_sameD, _sameT, _sameE, _sameA, _sameF, _sameS, _sameR, sameL, _sameH,
    _sameC, _sameP, _sameM, fields⟩ := carrier
  exact
    ⟨directedRoute, filterRoute, streamRoute, sealRoute, sealSame, sameL, fields⟩

theorem NetConvergenceCarrier_tail_window_real_seal_bridge
    {D T E A F S R L H C P M filterRead streamRead sealRead : BHist} :
    NetConvergenceCarrier D T E A F S R L H C P M →
      Cont D T E →
        Cont E F filterRead →
          Cont filterRead S streamRead →
            Cont F S streamRead →
              Cont streamRead R sealRead →
                hsame streamRead D →
                  hsame sealRead L →
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row D ∧ NetConvergenceCarrier D T E A F S R L H C P M)
                        (fun row : BHist =>
                          Cont D T E ∧ Cont E F filterRead ∧
                            Cont filterRead S streamRead ∧ hsame row D)
                        (fun row : BHist =>
                          Cont F S streamRead ∧ Cont streamRead R sealRead ∧
                            hsame sealRead L ∧ hsame row D ∧ hsame F F ∧ hsame S S ∧
                              hsame L L)
                        hsame ∧
                      Cont D T E ∧ Cont E F filterRead ∧ Cont filterRead S streamRead ∧
                        Cont F S streamRead ∧ Cont streamRead R sealRead ∧
                          hsame streamRead D ∧ hsame sealRead L ∧ hsame F F ∧
                            hsame S S ∧ hsame L L ∧
                              netConvergenceFields
                                  (NetConvergenceUp.mk D T E A F S R L H C P M) =
                                [D, T, E, A, F, S, R, L, H, C, P, M] := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  intro carrier directedRoute filterRoute windowRoute streamRoute sealRoute streamSame sealSame
  have tailAdmission :=
    NetConvergenceCarrier_tail_window_admission carrier directedRoute filterRoute windowRoute
      streamSame
  have sealAdmission :=
    NetConvergenceCarrier_real_seal_nonescape carrier directedRoute filterRoute streamRoute
      sealRoute sealSame
  obtain ⟨_sameD, _sameT, _sameE, sameF, sameS, _tailRoute, _filterRoute,
    _windowRoute, _streamSame, fields⟩ := tailAdmission
  obtain ⟨_directedRoute, _filterRouteForSeal, _streamRoute, _sealRoute, _sealSame,
    sameL, _fieldsForSeal⟩ := sealAdmission
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row D ∧ NetConvergenceCarrier D T E A F S R L H C P M)
          (fun row : BHist =>
            Cont D T E ∧ Cont E F filterRead ∧ Cont filterRead S streamRead ∧
              hsame row D)
          (fun row : BHist =>
            Cont F S streamRead ∧ Cont streamRead R sealRead ∧ hsame sealRead L ∧
              hsame row D ∧ hsame F F ∧ hsame S S ∧ hsame L L)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro D ⟨hsame_refl D, carrier⟩
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
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨directedRoute, filterRoute, windowRoute, source.left⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨streamRoute, sealRoute, sealSame, source.left, sameF, sameS, sameL⟩
  }
  exact
    ⟨cert, directedRoute, filterRoute, windowRoute, streamRoute, sealRoute, streamSame,
      sealSame, sameF, sameS, sameL, fields⟩

theorem NetConvergenceCarrier_filterbase_real_seal_finality_bridge
    {D T E A F S R L H C P M filterbaseRead handoffRead streamRead sealRead : BHist} :
    NetConvergenceCarrier D T E A F S R L H C P M →
      Cont D T E →
        Cont T E filterbaseRead →
          Cont E F handoffRead →
            Cont F S streamRead →
              Cont streamRead R sealRead →
                hsame filterbaseRead D →
                  hsame handoffRead F →
                    hsame sealRead L →
                      SemanticNameCert
                          (fun row : BHist =>
                            hsame row D ∧ NetConvergenceCarrier D T E A F S R L H C P M)
                          (fun row : BHist =>
                            Cont T E filterbaseRead ∧ Cont E F handoffRead ∧
                              hsame row D)
                          (fun _row : BHist =>
                            Cont F S streamRead ∧ Cont streamRead R sealRead ∧
                              hsame handoffRead F ∧ hsame sealRead L ∧ hsame F F ∧
                                hsame L L)
                          hsame ∧
                        Cont T E filterbaseRead ∧ Cont E F handoffRead ∧
                          Cont F S streamRead ∧ Cont streamRead R sealRead ∧
                            hsame handoffRead F ∧ hsame sealRead L ∧ hsame F F ∧
                              hsame L L ∧
                                netConvergenceFields
                                    (NetConvergenceUp.mk D T E A F S R L H C P M) =
                                  [D, T, E, A, F, S, R, L, H, C, P, M] := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  intro carrier directedRoute filterbaseRoute handoffRoute streamRoute sealRoute
    filterbaseSame handoffSame sealSame
  have filterbaseRows :=
    NetConvergenceCarrier_filterbase_finality carrier directedRoute filterbaseRoute
      handoffRoute filterbaseSame handoffSame
  have sealRows :=
    NetConvergenceCarrier_real_seal_nonescape carrier directedRoute handoffRoute
      streamRoute sealRoute sealSame
  obtain ⟨_sameD, _sameT, _sameE, sameF, _directedRoute, filterbaseRoute',
    handoffRoute', _filterbaseSame, handoffSame', fields⟩ := filterbaseRows
  obtain ⟨_directedRouteForSeal, _handoffRouteForSeal, streamRoute', sealRoute',
    sealSame', sameL, _fieldsForSeal⟩ := sealRows
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row D ∧ NetConvergenceCarrier D T E A F S R L H C P M)
          (fun row : BHist =>
            Cont T E filterbaseRead ∧ Cont E F handoffRead ∧ hsame row D)
          (fun _row : BHist =>
            Cont F S streamRead ∧ Cont streamRead R sealRead ∧ hsame handoffRead F ∧
              hsame sealRead L ∧ hsame F F ∧ hsame L L)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro D ⟨hsame_refl D, carrier⟩
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
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨filterbaseRoute', handoffRoute', source.left⟩
    ledger_sound := by
      intro _row _source
      exact ⟨streamRoute', sealRoute', handoffSame', sealSame', sameF, sameL⟩
  }
  exact
    ⟨cert, filterbaseRoute', handoffRoute', streamRoute', sealRoute', handoffSame',
      sealSame', sameF, sameL, fields⟩

theorem NetConvergenceCarrier_moore_smith_real_seal_handoff
    {D T E A F S R L H C P M sourceRead filterRead realRead streamRead sealRead : BHist} :
    NetConvergenceCarrier D T E A F S R L H C P M →
      Cont D A sourceRead →
        Cont sourceRead F filterRead →
          Cont filterRead L realRead →
            Cont F S streamRead →
              Cont streamRead R sealRead →
                hsame realRead D →
                  hsame sealRead L →
                    SemanticNameCert
                        (fun row : BHist =>
                          hsame row D ∧ NetConvergenceCarrier D T E A F S R L H C P M)
                        (fun row : BHist =>
                          Cont D A sourceRead ∧ Cont sourceRead F filterRead ∧
                            hsame row D)
                        (fun row : BHist =>
                          Cont filterRead L realRead ∧ Cont F S streamRead ∧
                            Cont streamRead R sealRead ∧ hsame realRead D ∧
                              hsame sealRead L ∧ hsame row D ∧ hsame A A ∧ hsame F F ∧
                                hsame L L)
                        hsame ∧
                      Cont D A sourceRead ∧ Cont sourceRead F filterRead ∧
                        Cont filterRead L realRead ∧ Cont F S streamRead ∧
                          Cont streamRead R sealRead ∧ hsame realRead D ∧ hsame sealRead L ∧
                            hsame A A ∧ hsame F F ∧ hsame L L ∧
                              netConvergenceFields
                                  (NetConvergenceUp.mk D T E A F S R L H C P M) =
                                [D, T, E, A, F, S, R, L, H, C, P, M] := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  intro carrier sourceRoute filterRoute realRoute streamRoute sealRoute realSame sealSame
  have mooreRows :=
    NetConvergenceCarrier_moore_smith_dependency carrier sourceRoute filterRoute realRoute
  obtain ⟨_sameD, sameA, sameF, sameL, sourceRoute', filterRoute', realRoute',
    fields⟩ := mooreRows
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row D ∧ NetConvergenceCarrier D T E A F S R L H C P M)
          (fun row : BHist =>
            Cont D A sourceRead ∧ Cont sourceRead F filterRead ∧ hsame row D)
          (fun row : BHist =>
            Cont filterRead L realRead ∧ Cont F S streamRead ∧
              Cont streamRead R sealRead ∧ hsame realRead D ∧ hsame sealRead L ∧
                hsame row D ∧ hsame A A ∧ hsame F F ∧ hsame L L)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro D ⟨hsame_refl D, carrier⟩
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
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨sourceRoute', filterRoute', source.left⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨realRoute', streamRoute, sealRoute, realSame, sealSame, source.left, sameA,
          sameF, sameL⟩
  }
  exact
    ⟨cert, sourceRoute', filterRoute', realRoute', streamRoute, sealRoute, realSame,
      sealSame, sameA, sameF, sameL, fields⟩

theorem NetConvergenceCarrier_moore_smith_real_seal_public_package
    {D T E A F S R L H C P M sourceRead filterRead realRead streamRead sealRead
      packageRead : BHist} :
    NetConvergenceCarrier D T E A F S R L H C P M →
      Cont D A sourceRead →
        Cont sourceRead F filterRead →
          Cont filterRead L realRead →
            Cont F S streamRead →
              Cont streamRead R sealRead →
                Cont sealRead H packageRead →
                  hsame realRead D →
                    hsame sealRead L →
                      hsame packageRead D →
                        SemanticNameCert
                            (fun row : BHist =>
                              hsame row packageRead ∧
                                NetConvergenceCarrier D T E A F S R L H C P M)
                            (fun row : BHist =>
                              Cont D A sourceRead ∧ Cont sourceRead F filterRead ∧
                                hsame row D)
                            (fun row : BHist =>
                              Cont filterRead L realRead ∧ Cont F S streamRead ∧
                                Cont streamRead R sealRead ∧ Cont sealRead H packageRead ∧
                                  hsame row D ∧ hsame H H ∧ hsame C C ∧ hsame P P ∧
                                    hsame M M)
                            hsame ∧
                          Cont D A sourceRead ∧ Cont sourceRead F filterRead ∧
                            Cont filterRead L realRead ∧ Cont F S streamRead ∧
                              Cont streamRead R sealRead ∧ Cont sealRead H packageRead ∧
                                hsame packageRead D ∧ hsame H H ∧ hsame C C ∧
                                  hsame P P ∧ hsame M M ∧
                                    netConvergenceFields
                                        (NetConvergenceUp.mk D T E A F S R L H C P M) =
                                      [D, T, E, A, F, S, R, L, H, C, P, M] := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  intro carrierRows sourceRoute filterRoute realRoute streamRoute sealRoute packageRoute realSame
    sealSame packageSame
  have handoffRows :=
    NetConvergenceCarrier_moore_smith_real_seal_handoff carrierRows sourceRoute filterRoute
      realRoute streamRoute sealRoute realSame sealSame
  obtain ⟨_handoffCert, sourceRoute', filterRoute', realRoute', streamRoute',
    sealRoute', _realSame, _sealSame, _sameA, _sameF, _sameL, fields⟩ := handoffRows
  have carrierWitness : NetConvergenceCarrier D T E A F S R L H C P M := carrierRows
  obtain ⟨_sameD, _sameT, _sameE, _sameA', _sameF', _sameS, _sameR, _sameL',
    sameH, sameC, sameP, sameM, _fieldsForCarrier⟩ := carrierRows
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row packageRead ∧ NetConvergenceCarrier D T E A F S R L H C P M)
          (fun row : BHist =>
            Cont D A sourceRead ∧ Cont sourceRead F filterRead ∧ hsame row D)
          (fun row : BHist =>
            Cont filterRead L realRead ∧ Cont F S streamRead ∧
              Cont streamRead R sealRead ∧ Cont sealRead H packageRead ∧ hsame row D ∧
                hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame M M)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro packageRead ⟨hsame_refl packageRead, carrierWitness⟩
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
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨sourceRoute', filterRoute', hsame_trans source.left packageSame⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨realRoute', streamRoute', sealRoute', packageRoute,
          hsame_trans source.left packageSame, sameH, sameC, sameP, sameM⟩
  }
  exact
    ⟨cert, sourceRoute', filterRoute', realRoute', streamRoute', sealRoute', packageRoute,
      packageSame, sameH, sameC, sameP, sameM, fields⟩

end BEDC.Derived.NetConvergenceUp
