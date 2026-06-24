import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ObserverPerspectiveClassifierCarrier [AskSetup] [PackageSetup]
    (observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory observerLeft ∧ UnaryHistory observerRight ∧
    UnaryHistory universeLeft ∧ UnaryHistory universeRight ∧ UnaryHistory locality ∧
      UnaryHistory gap ∧ UnaryHistory transport ∧ UnaryHistory route ∧
        UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont observerLeft observerRight universeLeft ∧
            Cont universeLeft universeRight locality ∧ Cont locality gap transport ∧
              Cont transport route gap ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg

theorem ObserverPerspectiveClassifierNonescape [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont observerLeft publicRead gap →
        PkgSig bundle publicRead pkg →
          UnaryHistory observerLeft ∧ UnaryHistory observerRight ∧
            UnaryHistory universeLeft ∧ UnaryHistory universeRight ∧ UnaryHistory locality ∧
              UnaryHistory gap ∧ UnaryHistory publicRead ∧ Cont observerLeft publicRead gap ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier observerPublicGap publicReadPkg
  obtain ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
    localityUnary, gapUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _observerUniverse, _universeLocality, _localityTransport, _transportGap, provenancePkg,
    namePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_right_factor observerPublicGap gapUnary
  exact
    ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
      localityUnary, gapUnary, publicReadUnary, observerPublicGap, provenancePkg, namePkg,
      publicReadPkg⟩

theorem ObserverPerspectiveClassifierLedgerExactness [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg ->
      Cont gap route publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory observerLeft ∧ UnaryHistory observerRight ∧
            UnaryHistory universeLeft ∧ UnaryHistory universeRight ∧ UnaryHistory locality ∧
              UnaryHistory gap ∧ UnaryHistory transport ∧ UnaryHistory route ∧
                UnaryHistory publicRead ∧ Cont observerLeft observerRight universeLeft ∧
                  Cont universeLeft universeRight locality ∧ Cont locality gap transport ∧
                    Cont transport route gap ∧ Cont gap route publicRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier gapRoutePublicRead publicReadPkg
  obtain ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
    localityUnary, gapUnary, transportUnary, routeUnary, _provenanceUnary, _nameUnary,
    observerUniverse, universeLocality, localityTransport, transportGap, provenancePkg,
    namePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed gapUnary routeUnary gapRoutePublicRead
  exact
    ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
      localityUnary, gapUnary, transportUnary, routeUnary, publicReadUnary, observerUniverse,
      universeLocality, localityTransport, transportGap, gapRoutePublicRead, provenancePkg,
      namePkg, publicReadPkg⟩

theorem ObserverPerspectiveClassifierLocalityCellComparison [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name comparison : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont locality gap comparison →
        UnaryHistory locality ∧ UnaryHistory gap ∧ UnaryHistory comparison ∧
          hsame comparison transport ∧ Cont universeLeft universeRight locality ∧
            Cont locality gap comparison ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro carrier localityGapComparison
  obtain ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary,
    _universeRightUnary, localityUnary, gapUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _observerUniverse, universeLocality, localityTransport,
    _transportGap, provenancePkg, namePkg⟩ := carrier
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed localityUnary gapUnary localityGapComparison
  have comparisonSameTransport : hsame comparison transport :=
    cont_deterministic localityGapComparison localityTransport
  exact
    ⟨localityUnary, gapUnary, comparisonUnary, comparisonSameTransport, universeLocality,
      localityGapComparison, provenancePkg, namePkg⟩

theorem ObserverPerspectiveClassifierCrossAlignmentLocalitySoundness [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name alignmentRead soundnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg ->
      Cont locality gap alignmentRead ->
        Cont alignmentRead transport soundnessRead ->
          PkgSig bundle soundnessRead pkg ->
            UnaryHistory locality ∧ UnaryHistory gap ∧ UnaryHistory alignmentRead ∧
              UnaryHistory soundnessRead ∧ hsame alignmentRead transport ∧
                Cont locality gap alignmentRead ∧ Cont alignmentRead transport soundnessRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle soundnessRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier localityGapAlignment alignmentTransportSoundness soundnessPkg
  obtain ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary,
    _universeRightUnary, localityUnary, gapUnary, transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _observerUniverse, _universeLocality, localityTransport,
    _transportGap, provenancePkg, namePkg⟩ := carrier
  have alignmentReadUnary : UnaryHistory alignmentRead :=
    unary_cont_closed localityUnary gapUnary localityGapAlignment
  have soundnessReadUnary : UnaryHistory soundnessRead :=
    unary_cont_closed alignmentReadUnary transportUnary alignmentTransportSoundness
  have alignmentSameTransport : hsame alignmentRead transport :=
    cont_deterministic localityGapAlignment localityTransport
  exact
    ⟨localityUnary, gapUnary, alignmentReadUnary, soundnessReadUnary,
      alignmentSameTransport, localityGapAlignment, alignmentTransportSoundness, provenancePkg,
      namePkg, soundnessPkg⟩

theorem ObserverPerspectiveClassifierAnchorChangeStability [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont observerLeft observerRight leftRead →
        Cont observerRight observerLeft rightRead →
          PkgSig bundle leftRead pkg →
            PkgSig bundle rightRead pkg →
              UnaryHistory observerLeft ∧ UnaryHistory observerRight ∧
                UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                  Cont observerLeft observerRight leftRead ∧
                    Cont observerRight observerLeft rightRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle leftRead pkg ∧ PkgSig bundle rightRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier leftAnchor rightAnchor leftPkg rightPkg
  obtain ⟨observerLeftUnary, observerRightUnary, _universeLeftUnary, _universeRightUnary,
    _localityUnary, _gapUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _observerUniverse, _universeLocality, _localityTransport, _transportGap, provenancePkg,
    namePkg⟩ := carrier
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed observerLeftUnary observerRightUnary leftAnchor
  have rightReadUnary : UnaryHistory rightRead :=
    unary_cont_closed observerRightUnary observerLeftUnary rightAnchor
  exact
    ⟨observerLeftUnary, observerRightUnary, leftReadUnary, rightReadUnary, leftAnchor,
      rightAnchor, provenancePkg, namePkg, leftPkg, rightPkg⟩

theorem ObserverPerspectiveClassifierLocalityRefinement [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality refinedLocality gap transport
      route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      hsame refinedLocality locality →
        Cont universeLeft universeRight refinedLocality →
          Cont refinedLocality gap transport →
            ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft
                universeRight refinedLocality gap transport route provenance name bundle pkg ∧
              UnaryHistory refinedLocality := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier sameRefinedLocality universeRefinedLocality refinedLocalityTransport
  obtain ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
    localityUnary, gapUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
    observerUniverse, _universeLocality, _localityTransport, transportGap, provenancePkg,
    namePkg⟩ := carrier
  have refinedLocalityUnary : UnaryHistory refinedLocality :=
    unary_transport_symm localityUnary sameRefinedLocality
  exact
    ⟨⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
        refinedLocalityUnary, gapUnary, transportUnary, routeUnary, provenanceUnary, nameUnary,
        observerUniverse, universeRefinedLocality, refinedLocalityTransport, transportGap,
        provenancePkg, namePkg⟩,
      refinedLocalityUnary⟩

theorem ObserverPerspectiveClassifierVerdictSourceExhaustion [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name publicRead verdict : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg ->
      Cont gap route publicRead ->
        Cont publicRead name verdict ->
          PkgSig bundle publicRead pkg ->
            PkgSig bundle verdict pkg ->
              UnaryHistory observerLeft ∧ UnaryHistory observerRight ∧
                UnaryHistory universeLeft ∧ UnaryHistory universeRight ∧
                  UnaryHistory locality ∧ UnaryHistory gap ∧ UnaryHistory transport ∧
                    UnaryHistory route ∧ UnaryHistory publicRead ∧ UnaryHistory verdict ∧
                      Cont gap route publicRead ∧ Cont publicRead name verdict ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle publicRead pkg ∧ PkgSig bundle verdict pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier gapRoutePublicRead publicReadNameVerdict publicReadPkg verdictPkg
  obtain ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
    localityUnary, gapUnary, transportUnary, routeUnary, _provenanceUnary, nameUnary,
    _observerUniverse, _universeLocality, _localityTransport, _transportGap, provenancePkg,
    namePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed gapUnary routeUnary gapRoutePublicRead
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed publicReadUnary nameUnary publicReadNameVerdict
  exact
    ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
      localityUnary, gapUnary, transportUnary, routeUnary, publicReadUnary, verdictUnary,
      gapRoutePublicRead, publicReadNameVerdict, provenancePkg, namePkg, publicReadPkg,
      verdictPkg⟩

theorem ObserverPerspectiveClassifierAlignmentLocalityCycle [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route provenance name
      alignmentRead cycleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight locality
        gap transport route provenance name bundle pkg →
      Cont locality gap alignmentRead →
        Cont transport route cycleRead →
          PkgSig bundle cycleRead pkg →
            UnaryHistory locality ∧ UnaryHistory gap ∧ UnaryHistory transport ∧
              UnaryHistory route ∧ UnaryHistory alignmentRead ∧ UnaryHistory cycleRead ∧
                hsame alignmentRead transport ∧ Cont locality gap alignmentRead ∧
                  Cont transport route cycleRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle cycleRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier alignmentRoute cycleRoute cyclePkg
  obtain ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary, _universeRightUnary,
    localityUnary, gapUnary, transportUnary, routeUnary, _provenanceUnary, _nameUnary,
    _observerUniverse, _universeLocality, localityTransport, _transportGap, provenancePkg,
    namePkg⟩ := carrier
  have alignmentReadUnary : UnaryHistory alignmentRead :=
    unary_cont_closed localityUnary gapUnary alignmentRoute
  have cycleReadUnary : UnaryHistory cycleRead :=
    unary_cont_closed transportUnary routeUnary cycleRoute
  have alignmentSameTransport : hsame alignmentRead transport :=
    cont_deterministic alignmentRoute localityTransport
  exact
    ⟨localityUnary, gapUnary, transportUnary, routeUnary, alignmentReadUnary,
      cycleReadUnary, alignmentSameTransport, alignmentRoute, cycleRoute, provenancePkg,
      namePkg, cyclePkg⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
