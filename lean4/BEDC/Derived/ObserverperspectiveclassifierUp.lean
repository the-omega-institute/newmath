import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem ObserverPerspectiveClassifierTwoObserverSourceAdmission [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name verdict : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont gap route verdict →
        PkgSig bundle verdict pkg →
          UnaryHistory observerLeft ∧ UnaryHistory observerRight ∧
            UnaryHistory universeLeft ∧ UnaryHistory universeRight ∧ UnaryHistory verdict ∧
              Cont observerLeft observerRight universeLeft ∧
                Cont universeLeft universeRight locality ∧ Cont gap route verdict ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle verdict pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier gapRouteVerdict verdictPkg
  obtain ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
    _localityUnary, gapUnary, _transportUnary, routeUnary, _provenanceUnary, _nameUnary,
    observerUniverse, universeLocality, _localityTransport, _transportGap, provenancePkg,
    namePkg⟩ := carrier
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed gapUnary routeUnary gapRouteVerdict
  exact
    ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
      verdictUnary, observerUniverse, universeLocality, gapRouteVerdict, provenancePkg,
      namePkg, verdictPkg⟩

theorem ObserverPerspectiveClassifierAlignmentTransportScope [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont transport route publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
                    hsame row route ∨ hsame row publicRead) ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
                  hsame row route ∨ hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont locality gap transport ∧
                  Cont transport route publicRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory transport ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier transportRoutePublic publicReadPkg
  obtain ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary,
    _universeRightUnary, localityUnary, gapUnary, transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _observerUniverse, _universeLocality,
    localityTransport, _transportGap, provenancePkg, namePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed transportUnary routeUnary transportRoutePublic
  let SourceSpec : BHist → Prop := fun row =>
    (hsame row locality ∨ hsame row gap ∨ hsame row transport ∨ hsame row route ∨
        hsame row publicRead) ∧ UnaryHistory row
  let PatternSpec : BHist → Prop := fun row =>
    hsame row locality ∨ hsame row gap ∨ hsame row transport ∨ hsame row route ∨
      hsame row publicRead
  let LedgerPolicy : BHist → Prop := fun row =>
    UnaryHistory row ∧ Cont locality gap transport ∧ Cont transport route publicRead ∧
      PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
        PkgSig bundle publicRead pkg
  have sourceTransport : SourceSpec transport :=
    ⟨Or.inr (Or.inr (Or.inl (hsame_refl transport))), transportUnary⟩
  have cert : SemanticNameCert SourceSpec PatternSpec LedgerPolicy hsame :=
    { core :=
        { carrier_inhabited := ⟨transport, sourceTransport⟩
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other sameRows
            exact hsame_symm sameRows
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row other sameRows sourceRow
            exact
              ⟨Or.elim sourceRow.left
                  (fun rowLocality =>
                    Or.inl (hsame_trans (hsame_symm sameRows) rowLocality))
                  (fun sourceTail =>
                    Or.elim sourceTail
                      (fun rowGap =>
                        Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowGap)))
                      (fun sourceTail =>
                        Or.elim sourceTail
                          (fun rowTransport =>
                            Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) rowTransport))))
                          (fun sourceTail =>
                            Or.elim sourceTail
                              (fun rowRoute =>
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) rowRoute)))))
                              (fun rowPublic =>
                                Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (hsame_trans (hsame_symm sameRows) rowPublic)))))))),
                unary_transport sourceRow.right sameRows⟩ }
      pattern_sound := by
        intro _row sourceRow
        exact sourceRow.left
      ledger_sound := by
        intro row sourceRow
        exact
          ⟨sourceRow.right, localityTransport, transportRoutePublic, provenancePkg, namePkg,
            publicReadPkg⟩ }
  exact ⟨cert, transportUnary, publicReadUnary⟩

theorem ObserverPerspectiveClassifierBHistScope [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont gap route scopedRead →
        PkgSig bundle scopedRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row observerLeft ∨ hsame row observerRight ∨
                  hsame row universeLeft ∨ hsame row universeRight ∨
                    hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
                      hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                        hsame row scopedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont gap route scopedRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle scopedRead pkg)
              hsame ∧
            UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier gapRouteScoped scopedReadPkg
  obtain ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary,
    _universeRightUnary, _localityUnary, gapUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _observerUniverse, _universeLocality, _localityTransport,
    _transportGap, provenancePkg, namePkg⟩ := carrier
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed gapUnary routeUnary gapRouteScoped
  let SourceSpec : BHist → Prop := fun row => hsame row scopedRead ∧ UnaryHistory row
  let PatternSpec : BHist → Prop := fun row =>
    hsame row observerLeft ∨ hsame row observerRight ∨ hsame row universeLeft ∨
      hsame row universeRight ∨ hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
        hsame row route ∨ hsame row provenance ∨ hsame row name ∨ hsame row scopedRead
  let LedgerPolicy : BHist → Prop := fun row =>
    UnaryHistory row ∧ Cont gap route scopedRead ∧ PkgSig bundle provenance pkg ∧
      PkgSig bundle name pkg ∧ PkgSig bundle scopedRead pkg
  have sourceScoped : SourceSpec scopedRead :=
    ⟨hsame_refl scopedRead, scopedReadUnary⟩
  have cert : SemanticNameCert SourceSpec PatternSpec LedgerPolicy hsame :=
    { core :=
        { carrier_inhabited := ⟨scopedRead, sourceScoped⟩
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other sameRows
            exact hsame_symm sameRows
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row other sameRows sourceRow
            exact
              ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
                unary_transport sourceRow.right sameRows⟩ }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr sourceRow.left)))))))))
      ledger_sound := by
        intro row sourceRow
        exact
          ⟨sourceRow.right, gapRouteScoped, provenancePkg, namePkg, scopedReadPkg⟩ }
  exact ⟨cert, scopedReadUnary⟩

theorem ObserverPerspectiveClassifierNameCertLedgerScope [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont gap route scopedRead →
        PkgSig bundle scopedRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row observerLeft ∨ hsame row observerRight ∨
                    hsame row universeLeft ∨ hsame row universeRight ∨
                      hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
                        hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                          hsame row scopedRead) ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row observerLeft ∨ hsame row observerRight ∨
                  hsame row universeLeft ∨ hsame row universeRight ∨
                    hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
                      hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                        hsame row scopedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont gap route scopedRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle scopedRead pkg)
              hsame ∧
            UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier gapRouteScoped scopedReadPkg
  obtain ⟨observerLeftUnary, _observerRightUnary, _universeLeftUnary,
    _universeRightUnary, _localityUnary, gapUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _observerUniverse, _universeLocality, _localityTransport,
    _transportGap, provenancePkg, namePkg⟩ := carrier
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed gapUnary routeUnary gapRouteScoped
  let PatternSpec : BHist → Prop := fun row =>
    hsame row observerLeft ∨ hsame row observerRight ∨ hsame row universeLeft ∨
      hsame row universeRight ∨ hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
        hsame row route ∨ hsame row provenance ∨ hsame row name ∨ hsame row scopedRead
  let SourceSpec : BHist → Prop := fun row => PatternSpec row ∧ UnaryHistory row
  let LedgerPolicy : BHist → Prop := fun row =>
    UnaryHistory row ∧ Cont gap route scopedRead ∧ PkgSig bundle provenance pkg ∧
      PkgSig bundle name pkg ∧ PkgSig bundle scopedRead pkg
  have sourceObserverLeft : SourceSpec observerLeft :=
    ⟨Or.inl (hsame_refl observerLeft), observerLeftUnary⟩
  have cert : SemanticNameCert SourceSpec PatternSpec LedgerPolicy hsame :=
    { core :=
        { carrier_inhabited := ⟨observerLeft, sourceObserverLeft⟩
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other sameRows
            exact hsame_symm sameRows
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro row other sameRows sourceRow
            cases sameRows
            exact sourceRow }
      pattern_sound := by
        intro _row sourceRow
        exact sourceRow.left
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, gapRouteScoped, provenancePkg, namePkg, scopedReadPkg⟩ }
  exact ⟨cert, scopedReadUnary⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
