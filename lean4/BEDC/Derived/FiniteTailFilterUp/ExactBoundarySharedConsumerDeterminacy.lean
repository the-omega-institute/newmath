import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterCarrier_exact_boundary_shared_consumer_determinacy
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRead realWindowRead exactBoundaryA exactBoundaryB
      terminalA terminalB : BHist}
    {bundle : ProbeBundle ProbeName} {pkgA pkgB : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRead ->
        Cont sealRead H realWindowRead ->
          UnaryHistory C ->
            Cont realWindowRead C exactBoundaryA ->
              Cont realWindowRead C exactBoundaryB ->
                Cont exactBoundaryA N terminalA ->
                  Cont exactBoundaryB N terminalB ->
                    PkgSig bundle terminalA pkgA ->
                      PkgSig bundle terminalB pkgB ->
                        hsame exactBoundaryA exactBoundaryB ∧ hsame terminalA terminalB ∧
                          UnaryHistory terminalA ∧ UnaryHistory terminalB := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier sealRoute realWindowRoute unaryC exactRouteA exactRouteB terminalRouteA
    terminalRouteB _pkgA _pkgB
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, _carrierUnaryC, routeR, routeQ,
    sameNE⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRead :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryRealWindow : UnaryHistory realWindowRead :=
    unary_cont_closed unarySeal unaryH realWindowRoute
  have unaryExactA : UnaryHistory exactBoundaryA :=
    unary_cont_closed unaryRealWindow unaryC exactRouteA
  have unaryExactB : UnaryHistory exactBoundaryB :=
    unary_cont_closed unaryRealWindow unaryC exactRouteB
  have unaryN : UnaryHistory N :=
    unary_transport unaryE (hsame_symm sameNE)
  have sameExact : hsame exactBoundaryA exactBoundaryB :=
    cont_deterministic exactRouteA exactRouteB
  have sameTerminal : hsame terminalA terminalB :=
    cont_respects_hsame sameExact (hsame_refl N) terminalRouteA terminalRouteB
  have unaryTerminalA : UnaryHistory terminalA :=
    unary_cont_closed unaryExactA unaryN terminalRouteA
  have unaryTerminalB : UnaryHistory terminalB :=
    unary_cont_closed unaryExactB unaryN terminalRouteB
  exact ⟨sameExact, sameTerminal, unaryTerminalA, unaryTerminalB⟩

end BEDC.Derived.FiniteTailFilterUp
