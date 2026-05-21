import BEDC.Derived.CriticalLineWitnessUp.RootPhaseRealSourceUnblock

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_gap_refusal_completeness
    {Z S M R Q H C P N zetaRead refusalRead gapRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S zetaRead →
        Cont N Q refusalRead →
          Cont refusalRead H gapRead →
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
              UnaryHistory N ∧ UnaryHistory zetaRead ∧ UnaryHistory refusalRead ∧
                UnaryHistory gapRead ∧ hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                  Cont N Q refusalRead ∧ Cont refusalRead H gapRead ∧ Cont M R Q ∧
                    Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory CriticalLineWitnessCarrier
  intro packet zetaRoute refusalRoute gapRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryZetaRead : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have unaryRefusalRead : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  have unaryGapRead : UnaryHistory gapRead :=
    unary_cont_closed unaryRefusalRead unaryH gapRoute
  exact
    ⟨unaryZ, unaryS, routeClosure.left, unaryH, routeClosure.right.right.left,
      unaryZetaRead, unaryRefusalRead, unaryGapRead, routeClosure.right.right.right,
      zetaRoute, refusalRoute, gapRoute, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessRootGapRefusalCompletenessPackage
    {Z S M R Q H C P N zetaRead sourceRead realWindow refusalRead boundaryRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead H sourceRead ->
          Cont M R realWindow ->
            Cont N Q refusalRead ->
              Cont refusalRead C boundaryRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                    (fun row : BHist => hsame row boundaryRead)
                    (fun row : BHist => hsame row boundaryRead ∧ Cont refusalRead C boundaryRead)
                    hsame ∧
                  UnaryHistory zetaRead ∧ UnaryHistory sourceRead ∧
                    UnaryHistory realWindow ∧ UnaryHistory refusalRead ∧
                      UnaryHistory boundaryRead ∧ hsame H (append Z S) ∧
                        Cont Z S zetaRead ∧ Cont zetaRead H sourceRead ∧
                          Cont M R realWindow ∧ Cont N Q refusalRead ∧
                            Cont refusalRead C boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaRoute sourceRoute realWindowRoute refusalRoute boundaryRoute
  have sourceReadiness :=
    CriticalLineWitnessRootZetaRealRatSourceReadiness packet zetaRoute sourceRoute
      realWindowRoute
  have refusalBoundary :=
    CriticalLineWitnessCarrier_root_unblock_refusal_boundary packet refusalRoute boundaryRoute
  obtain
    ⟨_unaryZ, _unaryS, _unaryM, _unaryR, _unaryQ, _unaryH, unaryZetaRead,
      unarySourceRead, unaryRealWindow, sameH, zetaRouteOut, sourceRouteOut, _routeQ,
      realWindowRouteOut, _routeC, _routeN⟩ := sourceReadiness
  obtain
    ⟨cert, _unaryZRefusal, _unarySRefusal, _unaryMRefusal, _unaryRRefusal,
      _unaryQRefusal, _unaryC, _unaryN, unaryRefusalRead, unaryBoundaryRead,
      _sameHRefusal, _routeQRefusal, _routeCRefusal, _routeNRefusal, refusalRouteOut,
      boundaryRouteOut⟩ := refusalBoundary
  exact
    ⟨cert, unaryZetaRead, unarySourceRead, unaryRealWindow, unaryRefusalRead,
      unaryBoundaryRead, sameH, zetaRouteOut, sourceRouteOut, realWindowRouteOut,
      refusalRouteOut, boundaryRouteOut⟩

end BEDC.Derived.CriticalLineWitnessUp
