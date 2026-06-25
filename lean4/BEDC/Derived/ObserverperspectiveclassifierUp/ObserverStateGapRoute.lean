import BEDC.Derived.ObserverperspectiveclassifierUp

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierObserverStateGapRoute [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name stateRead verdictRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont observerLeft observerRight stateRead →
        Cont stateRead gap verdictRead →
          PkgSig bundle verdictRead pkg →
            UnaryHistory observerLeft ∧ UnaryHistory observerRight ∧ UnaryHistory stateRead ∧
              UnaryHistory gap ∧ UnaryHistory verdictRead ∧
                Cont observerLeft observerRight stateRead ∧ Cont stateRead gap verdictRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle verdictRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier stateRoute verdictRoute verdictPkg
  obtain ⟨observerLeftUnary, observerRightUnary, _universeLeftUnary, _universeRightUnary,
    _localityUnary, gapUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _observerUniverse, _universeLocality, _localityTransport, _transportGap, provenancePkg,
    namePkg⟩ := carrier
  have stateReadUnary : UnaryHistory stateRead :=
    unary_cont_closed observerLeftUnary observerRightUnary stateRoute
  have verdictReadUnary : UnaryHistory verdictRead :=
    unary_cont_closed stateReadUnary gapUnary verdictRoute
  exact
    ⟨observerLeftUnary, observerRightUnary, stateReadUnary, gapUnary, verdictReadUnary,
      stateRoute, verdictRoute, provenancePkg, namePkg, verdictPkg⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
