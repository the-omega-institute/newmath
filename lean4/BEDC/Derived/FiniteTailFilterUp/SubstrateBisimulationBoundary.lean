import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterCarrier_substrate_bisimulation_boundary
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N substrateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont S D R ->
        Cont R B Q ->
          Cont Q E substrateRead ->
            PkgSig bundle substrateRead pkg ->
              UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory Q ∧
                UnaryHistory E ∧ UnaryHistory substrateRead ∧ Cont S D R ∧
                  Cont R B Q ∧ Cont Q E substrateRead ∧ hsame N E ∧
                    PkgSig bundle substrateRead pkg := by
  -- BEDC touchpoint anchor: FiniteTailFilterCarrier BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier routeR routeQ substrateRoute substratePkg
  obtain ⟨unaryS, unaryD, _unaryB, unaryE, _unaryH, _unaryC, _carrierRouteR,
    _carrierRouteQ, sameN⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR _unaryB routeQ
  have substrateUnary : UnaryHistory substrateRead :=
    unary_cont_closed unaryQ unaryE substrateRoute
  exact
    ⟨unaryS, unaryD, unaryR, unaryQ, unaryE, substrateUnary, routeR, routeQ,
      substrateRoute, sameN, substratePkg⟩

end BEDC.Derived.FiniteTailFilterUp
