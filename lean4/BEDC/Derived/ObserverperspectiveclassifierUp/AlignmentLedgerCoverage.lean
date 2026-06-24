import BEDC.Derived.ObserverperspectiveclassifierUp

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierAlignmentLedgerCoverage [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route provenance
      name alignmentRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont locality gap alignmentRead →
        Cont transport route consumerRead →
          PkgSig bundle consumerRead pkg →
            UnaryHistory locality ∧ UnaryHistory gap ∧ UnaryHistory transport ∧
              UnaryHistory route ∧ UnaryHistory alignmentRead ∧ UnaryHistory consumerRead ∧
                hsame alignmentRead transport ∧ Cont locality gap alignmentRead ∧
                  Cont transport route consumerRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier localityGapAlignment transportRouteConsumer consumerPkg
  obtain
    ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary, _universeRightUnary,
      localityUnary, gapUnary, transportUnary, routeUnary, _provenanceUnary, _nameUnary,
      _observerUniverse, _universeLocality, localityTransport, _transportGap, provenancePkg,
      namePkg⟩ := carrier
  have alignmentUnary : UnaryHistory alignmentRead :=
    unary_cont_closed localityUnary gapUnary localityGapAlignment
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed transportUnary routeUnary transportRouteConsumer
  have alignmentSameTransport : hsame alignmentRead transport :=
    cont_deterministic localityGapAlignment localityTransport
  exact
    ⟨localityUnary, gapUnary, transportUnary, routeUnary, alignmentUnary, consumerUnary,
      alignmentSameTransport, localityGapAlignment, transportRouteConsumer, provenancePkg,
      namePkg, consumerPkg⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
