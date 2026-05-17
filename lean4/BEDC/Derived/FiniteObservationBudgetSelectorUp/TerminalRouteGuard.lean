import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteObservationBudgetSelectorCarrier_terminal_route_guard
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N terminalA terminalB guardA guardB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N →
      Cont R E terminalA →
        Cont R E terminalB →
          Cont terminalA N guardA →
            Cont terminalB N guardB →
              PkgSig bundle guardA pkg →
                PkgSig bundle guardB pkg →
                  UnaryHistory terminalA ∧ UnaryHistory terminalB ∧
                    UnaryHistory guardA ∧ UnaryHistory guardB ∧
                      hsame terminalA terminalB ∧ hsame guardA guardB ∧
                        Cont B S W ∧ Cont W D R ∧ Cont R E terminalA ∧
                          Cont terminalA N guardA ∧ hsame N E ∧
                            PkgSig bundle guardA pkg ∧ PkgSig bundle guardB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier terminalRouteA terminalRouteB guardRouteA guardRouteB guardPkgA guardPkgB
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, routeW, routeR, _routeC,
    sameName⟩ := carrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS routeW
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD routeR
  have unaryTerminalA : UnaryHistory terminalA :=
    unary_cont_closed unaryR unaryE terminalRouteA
  have sameTerminal : hsame terminalA terminalB :=
    cont_deterministic terminalRouteA terminalRouteB
  have unaryTerminalB : UnaryHistory terminalB :=
    unary_transport unaryTerminalA sameTerminal
  have unaryGuardA : UnaryHistory guardA :=
    unary_cont_closed unaryTerminalA unaryE (by
      cases sameName
      exact guardRouteA)
  have sameGuard : hsame guardA guardB :=
    cont_respects_hsame sameTerminal (hsame_refl N) guardRouteA guardRouteB
  have unaryGuardB : UnaryHistory guardB :=
    unary_transport unaryGuardA sameGuard
  exact
    ⟨unaryTerminalA, unaryTerminalB, unaryGuardA, unaryGuardB, sameTerminal,
      sameGuard, routeW, routeR, terminalRouteA, guardRouteA, sameName, guardPkgA,
      guardPkgB⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
