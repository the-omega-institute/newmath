import BEDC.Derived.ObserverperspectiveclassifierUp

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierTwoStateNoConfusion [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont observerLeft universeLeft leftRead →
        Cont observerRight universeRight rightRead →
          hsame leftRead rightRead →
            UnaryHistory observerLeft ∧ UnaryHistory observerRight ∧
              UnaryHistory leftRead ∧ UnaryHistory rightRead ∧ hsame leftRead rightRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig UnaryHistory
  intro carrier leftObserverRead rightObserverRead sameReads
  obtain
    ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
      _localityUnary, _gapUnary, _transportUnary, _routeUnary, _provenanceUnary,
      _nameUnary, _observerUniverse, _universeLocality, _localityTransport, _transportGap,
      provenancePkg, namePkg⟩ := carrier
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed observerLeftUnary universeLeftUnary leftObserverRead
  have rightReadUnary : UnaryHistory rightRead :=
    unary_cont_closed observerRightUnary universeRightUnary rightObserverRead
  exact
    ⟨observerLeftUnary, observerRightUnary, leftReadUnary, rightReadUnary, sameReads,
      provenancePkg, namePkg⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
