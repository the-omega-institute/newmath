import BEDC.Derived.ObserverperspectiveclassifierUp

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierPerspectiveStability [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name swappedObserverRead swappedUniverseRead swappedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont observerRight observerLeft swappedObserverRead →
        Cont universeRight universeLeft swappedUniverseRead →
          Cont swappedUniverseRead locality swappedRoute →
            PkgSig bundle swappedRoute pkg →
              UnaryHistory observerLeft ∧ UnaryHistory observerRight ∧
                UnaryHistory universeLeft ∧ UnaryHistory universeRight ∧
                  UnaryHistory locality ∧ UnaryHistory swappedObserverRead ∧
                    UnaryHistory swappedUniverseRead ∧ UnaryHistory swappedRoute ∧
                      Cont observerRight observerLeft swappedObserverRead ∧
                        Cont universeRight universeLeft swappedUniverseRead ∧
                          Cont swappedUniverseRead locality swappedRoute ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle swappedRoute pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier swappedObserverRoute swappedUniverseRoute swappedLocalityRoute swappedPkg
  obtain
    ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
      localityUnary, _gapUnary, _transportUnary, _routeUnary, _provenanceUnary,
      _nameUnary, _observerUniverse, _universeLocality, _localityTransport, _transportGap,
      provenancePkg, namePkg⟩ := carrier
  have swappedObserverUnary : UnaryHistory swappedObserverRead :=
    unary_cont_closed observerRightUnary observerLeftUnary swappedObserverRoute
  have swappedUniverseUnary : UnaryHistory swappedUniverseRead :=
    unary_cont_closed universeRightUnary universeLeftUnary swappedUniverseRoute
  have swappedRouteUnary : UnaryHistory swappedRoute :=
    unary_cont_closed swappedUniverseUnary localityUnary swappedLocalityRoute
  exact
    ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
      localityUnary, swappedObserverUnary, swappedUniverseUnary, swappedRouteUnary,
      swappedObserverRoute, swappedUniverseRoute, swappedLocalityRoute, provenancePkg,
      namePkg, swappedPkg⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
