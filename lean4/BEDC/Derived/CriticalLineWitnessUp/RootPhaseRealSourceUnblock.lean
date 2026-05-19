import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessRootZetaRealRatSourceReadiness
    {Z S M R Q H C P N zetaRead sourceRead realWindow : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead H sourceRead ->
          Cont M R realWindow ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory zetaRead ∧
                UnaryHistory sourceRead ∧ UnaryHistory realWindow ∧ hsame H (append Z S) ∧
                  Cont Z S zetaRead ∧ Cont zetaRead H sourceRead ∧ Cont M R Q ∧
                    Cont M R realWindow ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zetaRoute sourceRoute realWindowRoute
  have zetaSource :=
    CriticalLineWitnessCarrier_root_zeta_source_obligation packet zetaRoute sourceRoute
  have realWindowPack :=
    CriticalLineWitnessCarrier_root_real_window_obligation packet realWindowRoute
  obtain
    ⟨unaryZ, unaryS, _unaryQFromSource, unaryH, unaryZetaRead, unarySourceRead, sameH,
      zetaRouteOut, sourceRouteOut, _routeQFromSource, routeC, routeN⟩ := zetaSource
  obtain
    ⟨unaryM, unaryR, unaryQ, _unaryHFromReal, _unaryC, _unaryN, unaryRealWindow, _sameH,
      routeQ, realWindowRouteOut, _routeC, _routeN⟩ := realWindowPack
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryZetaRead, unarySourceRead,
      unaryRealWindow, sameH, zetaRouteOut, sourceRouteOut, routeQ, realWindowRouteOut,
      routeC, routeN⟩

theorem CriticalLineWitnessRootDownstreamUnblockPackage
    {Z S M R Q H C P N zetaRead sourceRead realWindow refusalRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead H sourceRead ->
          Cont M R realWindow ->
            Cont N Q refusalRead ->
              Cont refusalRead C boundaryRead ->
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                  UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
                    UnaryHistory zetaRead ∧ UnaryHistory sourceRead ∧ UnaryHistory realWindow ∧
                      UnaryHistory refusalRead ∧ UnaryHistory boundaryRead ∧
                        hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                          Cont zetaRead H sourceRead ∧ Cont M R Q ∧
                            Cont M R realWindow ∧ Cont Q H C ∧ Cont C P N ∧
                              Cont N Q refusalRead ∧ Cont refusalRead C boundaryRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro packet zetaRoute sourceRoute realWindowRoute refusalRoute boundaryRoute
  have sourceReadiness :=
    CriticalLineWitnessRootZetaRealRatSourceReadiness packet zetaRoute sourceRoute
      realWindowRoute
  have refusalBoundary :=
    CriticalLineWitnessCarrier_root_unblock_refusal_boundary packet refusalRoute boundaryRoute
  obtain
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryZetaRead, unarySourceRead,
      unaryRealWindow, sameH, zetaRouteOut, sourceRouteOut, routeQ, realWindowRouteOut,
      routeC, routeN⟩ := sourceReadiness
  obtain
    ⟨_cert, _unaryZRefusal, _unarySRefusal, _unaryMRefusal, _unaryRRefusal,
      _unaryQRefusal, unaryC, unaryN, unaryRefusalRead, unaryBoundaryRead, _sameHRefusal,
      _routeQRefusal, _routeCRefusal, _routeNRefusal, refusalRouteOut, boundaryRouteOut⟩ :=
    refusalBoundary
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN, unaryZetaRead,
      unarySourceRead, unaryRealWindow, unaryRefusalRead, unaryBoundaryRead, sameH,
      zetaRouteOut, sourceRouteOut, routeQ, realWindowRouteOut, routeC, routeN,
      refusalRouteOut, boundaryRouteOut⟩

end BEDC.Derived.CriticalLineWitnessUp
