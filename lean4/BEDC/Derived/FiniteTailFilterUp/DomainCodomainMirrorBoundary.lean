import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterCarrier_domain_codomain_mirror_boundary
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N domainRead codomainRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont S D domainRead ->
        Cont domainRead E codomainRead ->
          PkgSig bundle codomainRead pkg ->
            UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory E ∧
              UnaryHistory domainRead ∧ UnaryHistory codomainRead ∧ hsame N E ∧
                Cont S D domainRead ∧ Cont domainRead E codomainRead ∧
                  PkgSig bundle codomainRead pkg := by
  -- BEDC touchpoint anchor: FiniteTailFilterCarrier BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier domainRoute codomainRoute codomainPkg
  obtain ⟨unaryS, unaryD, _unaryB, unaryE, _unaryH, _unaryC, _routeR, _routeQ,
    sameN⟩ := carrier
  have domainUnary : UnaryHistory domainRead :=
    unary_cont_closed unaryS unaryD domainRoute
  have codomainUnary : UnaryHistory codomainRead :=
    unary_cont_closed domainUnary unaryE codomainRoute
  exact
    ⟨unaryS, unaryD, unaryE, domainUnary, codomainUnary, sameN, domainRoute,
      codomainRoute, codomainPkg⟩

end BEDC.Derived.FiniteTailFilterUp
