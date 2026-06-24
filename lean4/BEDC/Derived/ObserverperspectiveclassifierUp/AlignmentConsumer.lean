import BEDC.Derived.ObserverperspectiveclassifierUp

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierAlignmentConsumer [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont transport route publicRead →
        PkgSig bundle publicRead pkg →
          UnaryHistory locality ∧ UnaryHistory gap ∧ UnaryHistory transport ∧
            UnaryHistory route ∧ UnaryHistory publicRead ∧ Cont locality gap transport ∧
              Cont transport route publicRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier transportRoutePublicRead publicReadPkg
  obtain
    ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary, _universeRightUnary,
      localityUnary, gapUnary, transportUnary, routeUnary, _provenanceUnary, _nameUnary,
      _observerUniverse, _universeLocality, localityTransport, _transportGap, provenancePkg,
      namePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed transportUnary routeUnary transportRoutePublicRead
  exact
    ⟨localityUnary, gapUnary, transportUnary, routeUnary, publicReadUnary, localityTransport,
      transportRoutePublicRead, provenancePkg, namePkg, publicReadPkg⟩

theorem ObserverPerspectiveClassifierLedgerExhaustion [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name publicRead verdict : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont gap route publicRead →
        Cont publicRead name verdict →
          PkgSig bundle publicRead pkg →
            PkgSig bundle verdict pkg →
              UnaryHistory publicRead ∧ UnaryHistory verdict ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle publicRead pkg ∧ PkgSig bundle verdict pkg ∧
                    hsame verdict verdict := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier gapRoutePublicRead publicReadNameVerdict publicReadPkg verdictPkg
  obtain
    ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary, _universeRightUnary,
      _localityUnary, gapUnary, _transportUnary, routeUnary, _provenanceUnary, nameUnary,
      _observerUniverse, _universeLocality, _localityTransport, _transportGap, provenancePkg,
      namePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed gapUnary routeUnary gapRoutePublicRead
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed publicReadUnary nameUnary publicReadNameVerdict
  exact
    ⟨publicReadUnary, verdictUnary, provenancePkg, namePkg, publicReadPkg, verdictPkg,
      hsame_refl verdict⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
