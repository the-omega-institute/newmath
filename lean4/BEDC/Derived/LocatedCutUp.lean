import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedCutUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedCutCarrier [AskSetup] [PackageSetup]
    (lower upper window handoff sealRow transportRow route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont lower upper window ∧
    Cont window handoff transportRow ∧
      Cont transportRow route provenance ∧
        Cont provenance localCert sealRow ∧
          PkgSig bundle provenance pkg ∧ hsame sealRow handoff ∧ hsame sealRow provenance

theorem LocatedCutCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
            bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
            bundle pkg ∧ hsame row handoff)
        (fun row : BHist =>
          LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
            bundle pkg ∧ hsame row provenance)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRow (And.intro carrier (hsame_refl sealRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact And.intro source.left
        (hsame_trans source.right source.left.right.right.right.right.right.left)
    ledger_sound := by
      intro _row source
      exact And.intro source.left
        (hsame_trans source.right source.left.right.right.right.right.right.right)
  }

theorem LocatedCutCarrier_seal_boundary_exactness [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      hsame handoff provenance ∧ Cont window handoff transportRow ∧
        Cont provenance localCert sealRow ∧ PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨_windowRoute, handoffRoute, _provenanceRoute, sealRoute, packageSig, sameSealHandoff,
    sameSealProvenance⟩ := carrier
  have sameHandoffProvenance : hsame handoff provenance :=
    hsame_trans (hsame_symm sameSealHandoff) sameSealProvenance
  exact ⟨sameHandoffProvenance, handoffRoute, sealRoute, packageSig⟩

theorem LocatedCutCarrier_classifier_transport [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert lower' upper'
      window' handoff' sealRow' transportRow' route' provenance' localCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance
        localCert bundle pkg ->
      hsame lower lower' ->
        hsame upper upper' ->
          hsame handoff handoff' ->
            hsame route route' ->
              hsame localCert localCert' ->
                Cont lower' upper' window' ->
                  Cont window' handoff' transportRow' ->
                    Cont transportRow' route' provenance' ->
                      Cont provenance' localCert' sealRow' ->
                        PkgSig bundle provenance' pkg ->
                          LocatedCutCarrier lower' upper' window' handoff' sealRow'
                              transportRow' route' provenance' localCert' bundle pkg ∧
                            hsame window window' ∧ hsame transportRow transportRow' ∧
                              hsame provenance provenance' ∧ hsame sealRow sealRow' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameLower sameUpper sameHandoff sameRoute sameLocalCert lowerUpperWindow'
    windowHandoffTransport' transportRouteProvenance' provenanceLocalCertSeal'
    provenancePkg'
  obtain ⟨lowerUpperWindow, windowHandoffTransport, transportRouteProvenance,
    provenanceLocalCertSeal, _provenancePkg, sameSealHandoff, sameSealProvenance⟩ :=
    carrier
  have sameWindow : hsame window window' :=
    cont_respects_hsame sameLower sameUpper lowerUpperWindow lowerUpperWindow'
  have sameTransportRow : hsame transportRow transportRow' :=
    cont_respects_hsame sameWindow sameHandoff windowHandoffTransport windowHandoffTransport'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransportRow sameRoute transportRouteProvenance
      transportRouteProvenance'
  have sameSealRow : hsame sealRow sealRow' :=
    cont_respects_hsame sameProvenance sameLocalCert provenanceLocalCertSeal
      provenanceLocalCertSeal'
  have sameSealHandoff' : hsame sealRow' handoff' :=
    hsame_trans (hsame_symm sameSealRow) (hsame_trans sameSealHandoff sameHandoff)
  have sameSealProvenance' : hsame sealRow' provenance' :=
    hsame_trans (hsame_symm sameSealRow) (hsame_trans sameSealProvenance sameProvenance)
  have transported :
      LocatedCutCarrier lower' upper' window' handoff' sealRow' transportRow' route'
          provenance' localCert' bundle pkg :=
    ⟨lowerUpperWindow', windowHandoffTransport', transportRouteProvenance',
      provenanceLocalCertSeal', provenancePkg', sameSealHandoff', sameSealProvenance'⟩
  exact ⟨transported, sameWindow, sameTransportRow, sameProvenance, sameSealRow⟩

theorem LocatedCutCarrier_located_window_exactness [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          UnaryHistory handoff ->
            UnaryHistory route ->
              UnaryHistory localCert ->
                UnaryHistory window ∧ UnaryHistory transportRow ∧ UnaryHistory provenance ∧
                  UnaryHistory sealRow ∧ Cont lower upper window ∧
                    Cont window handoff transportRow ∧
                      Cont transportRow route provenance ∧
                        Cont provenance localCert sealRow ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier lowerUnary upperUnary handoffUnary routeUnary localCertUnary
  obtain ⟨lowerUpperWindow, windowHandoffTransport, transportRouteProvenance,
    provenanceLocalCertSeal, provenancePkg, _sameSealHandoff, _sameSealProvenance⟩ :=
    carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed lowerUnary upperUnary lowerUpperWindow
  have transportUnary : UnaryHistory transportRow :=
    unary_cont_closed windowUnary handoffUnary windowHandoffTransport
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportUnary routeUnary transportRouteProvenance
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed provenanceUnary localCertUnary provenanceLocalCertSeal
  exact ⟨windowUnary, transportUnary, provenanceUnary, sealUnary, lowerUpperWindow,
    windowHandoffTransport, transportRouteProvenance, provenanceLocalCertSeal, provenancePkg⟩

theorem LocatedCutCarrier_window_handoff_totality [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          UnaryHistory handoff ->
            UnaryHistory route ->
              UnaryHistory localCert ->
                Cont handoff route consumer ->
                  PkgSig bundle consumer pkg ->
                    UnaryHistory consumer ∧ Cont lower upper window ∧
                      Cont window handoff transportRow ∧ Cont transportRow route provenance ∧
                        Cont handoff route consumer ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle consumer pkg ∧ hsame sealRow handoff := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier _lowerUnary _upperUnary handoffUnary routeUnary _localCertUnary handoffRouteConsumer
    consumerPkg
  obtain ⟨lowerUpperWindow, windowHandoffTransport, transportRouteProvenance,
    _provenanceLocalCertSeal, provenancePkg, sameSealHandoff, _sameSealProvenance⟩ :=
    carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary routeUnary handoffRouteConsumer
  exact ⟨consumerUnary, lowerUpperWindow, windowHandoffTransport, transportRouteProvenance,
    handoffRouteConsumer, provenancePkg, consumerPkg, sameSealHandoff⟩

theorem LocatedCutCarrier_regular_cauchy_handoff [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          UnaryHistory handoff ->
            UnaryHistory route ->
              UnaryHistory localCert ->
                Cont handoff route consumer ->
                  PkgSig bundle consumer pkg ->
                    UnaryHistory consumer ∧ Cont lower upper window ∧
                      Cont window handoff transportRow ∧ Cont handoff route consumer ∧
                        PkgSig bundle provenance pkg ∧ hsame sealRow handoff := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier _lowerUnary _upperUnary handoffUnary routeUnary _localCertUnary handoffRouteConsumer
    _consumerPkg
  obtain ⟨lowerUpperWindow, windowHandoffTransport, _transportRouteProvenance,
    _provenanceLocalCertSeal, provenancePkg, sameSealHandoff, _sameSealProvenance⟩ :=
    carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary routeUnary handoffRouteConsumer
  exact ⟨consumerUnary, lowerUpperWindow, windowHandoffTransport, handoffRouteConsumer,
    provenancePkg, sameSealHandoff⟩

theorem LocatedCutCarrier_dyadic_interval_exhaustion [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          UnaryHistory handoff ->
            UnaryHistory route ->
              UnaryHistory localCert ->
                UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory window ∧
                  UnaryHistory transportRow ∧ UnaryHistory provenance ∧
                    UnaryHistory sealRow ∧ Cont lower upper window ∧
                      Cont window handoff transportRow ∧
                        Cont transportRow route provenance ∧
                          Cont provenance localCert sealRow ∧ PkgSig bundle provenance pkg ∧
                            hsame handoff provenance := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier lowerUnary upperUnary handoffUnary routeUnary localCertUnary
  obtain ⟨lowerUpperWindow, windowHandoffTransport, transportRouteProvenance,
    provenanceLocalCertSeal, provenancePkg, sameSealHandoff, sameSealProvenance⟩ :=
    carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed lowerUnary upperUnary lowerUpperWindow
  have transportUnary : UnaryHistory transportRow :=
    unary_cont_closed windowUnary handoffUnary windowHandoffTransport
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportUnary routeUnary transportRouteProvenance
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed provenanceUnary localCertUnary provenanceLocalCertSeal
  have sameHandoffProvenance : hsame handoff provenance :=
    hsame_trans (hsame_symm sameSealHandoff) sameSealProvenance
  exact
    ⟨lowerUnary, upperUnary, windowUnary, transportUnary, provenanceUnary, sealUnary,
      lowerUpperWindow, windowHandoffTransport, transportRouteProvenance,
      provenanceLocalCertSeal, provenancePkg, sameHandoffProvenance⟩

theorem LocatedCutCarrier_common_window_refinement [AskSetup] [PackageSetup]
    {lower upper window₁ window₂ handoff sealRow₁ sealRow₂ transportRow₁ transportRow₂
      route provenance₁ provenance₂ localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window₁ handoff sealRow₁ transportRow₁ route provenance₁
        localCert bundle pkg ->
      LocatedCutCarrier lower upper window₂ handoff sealRow₂ transportRow₂ route provenance₂
          localCert bundle pkg ->
        hsame window₁ window₂ ∧ hsame transportRow₁ transportRow₂ ∧
          hsame provenance₁ provenance₂ ∧ hsame sealRow₁ sealRow₂ ∧
            Cont lower upper window₁ ∧ Cont lower upper window₂ := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier₁ carrier₂
  obtain ⟨lowerUpperWindow₁, windowHandoffTransport₁, transportRouteProvenance₁,
    provenanceLocalCertSeal₁, _provenancePkg₁, _sameSealHandoff₁,
    _sameSealProvenance₁⟩ := carrier₁
  obtain ⟨lowerUpperWindow₂, windowHandoffTransport₂, transportRouteProvenance₂,
    provenanceLocalCertSeal₂, _provenancePkg₂, _sameSealHandoff₂,
    _sameSealProvenance₂⟩ := carrier₂
  have sameWindow : hsame window₁ window₂ :=
    cont_respects_hsame (hsame_refl lower) (hsame_refl upper)
      lowerUpperWindow₁ lowerUpperWindow₂
  have sameTransport : hsame transportRow₁ transportRow₂ :=
    cont_respects_hsame sameWindow (hsame_refl handoff)
      windowHandoffTransport₁ windowHandoffTransport₂
  have sameProvenance : hsame provenance₁ provenance₂ :=
    cont_respects_hsame sameTransport (hsame_refl route)
      transportRouteProvenance₁ transportRouteProvenance₂
  have sameSeal : hsame sealRow₁ sealRow₂ :=
    cont_respects_hsame sameProvenance (hsame_refl localCert)
      provenanceLocalCertSeal₁ provenanceLocalCertSeal₂
  exact ⟨sameWindow, sameTransport, sameProvenance, sameSeal, lowerUpperWindow₁,
    lowerUpperWindow₂⟩

theorem LocatedCutCarrier_ledger_pair_coherence [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert paired : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          Cont lower upper paired ->
            PkgSig bundle paired pkg ->
              UnaryHistory paired ∧ Cont lower upper window ∧ Cont lower upper paired ∧
                hsame window paired ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle paired pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier lowerUnary upperUnary lowerUpperPaired pairedPkg
  obtain ⟨lowerUpperWindow, _windowHandoffTransport, _transportRouteProvenance,
    _provenanceLocalCertSeal, provenancePkg, _sameSealHandoff, _sameSealProvenance⟩ :=
    carrier
  have pairedUnary : UnaryHistory paired :=
    unary_cont_closed lowerUnary upperUnary lowerUpperPaired
  have sameWindowPaired : hsame window paired :=
    cont_respects_hsame (hsame_refl lower) (hsame_refl upper)
      lowerUpperWindow lowerUpperPaired
  exact
    ⟨pairedUnary, lowerUpperWindow, lowerUpperPaired, sameWindowPaired, provenancePkg,
      pairedPkg⟩

theorem LocatedCutCarrier_interval_witness_extraction [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          UnaryHistory handoff ->
            UnaryHistory route ->
              UnaryHistory localCert ->
                ∃ witness : BHist,
                  Cont lower upper witness ∧ UnaryHistory witness ∧ hsame witness window ∧
                    Cont window handoff transportRow ∧ hsame handoff provenance ∧
                      PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier lowerUnary upperUnary handoffUnary routeUnary localCertUnary
  have exhausted :=
    LocatedCutCarrier_dyadic_interval_exhaustion carrier lowerUnary upperUnary handoffUnary
      routeUnary localCertUnary
  obtain ⟨_lowerUnary, _upperUnary, windowUnary, _transportUnary, _provenanceUnary,
    _sealUnary, lowerUpperWindow, windowHandoffTransport, _transportRouteProvenance,
    _provenanceLocalCertSeal, provenancePkg, sameHandoffProvenance⟩ := exhausted
  exact ⟨window, lowerUpperWindow, windowUnary, hsame_refl window, windowHandoffTransport,
    sameHandoffProvenance, provenancePkg⟩

theorem LocatedCutCarrier_standard_bridge_boundary [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          UnaryHistory handoff ->
            UnaryHistory route ->
              UnaryHistory localCert ->
                Cont handoff sealRow bridge ->
                  PkgSig bundle bridge pkg ->
                    UnaryHistory bridge ∧ hsame handoff provenance ∧
                      Cont handoff sealRow bridge ∧ PkgSig bundle bridge pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier lowerUnary upperUnary handoffUnary routeUnary localCertUnary handoffSealBridge
    bridgePkg
  have exhausted :=
    LocatedCutCarrier_dyadic_interval_exhaustion carrier lowerUnary upperUnary handoffUnary
      routeUnary localCertUnary
  obtain ⟨_lowerUnary, _upperUnary, _windowUnary, _transportUnary, _provenanceUnary,
    sealUnary, _lowerUpperWindow, _windowHandoffTransport, _transportRouteProvenance,
    _provenanceLocalCertSeal, _provenancePkg, sameHandoffProvenance⟩ := exhausted
  have bridgeUnary : UnaryHistory bridge :=
    unary_cont_closed handoffUnary sealUnary handoffSealBridge
  exact ⟨bridgeUnary, sameHandoffProvenance, handoffSealBridge, bridgePkg⟩

theorem LocatedCutCarrier_window_monotonic_refinement [AskSetup] [PackageSetup]
    {lower upper coarseWindow narrowWindow handoff sealCoarse sealNarrow transportCoarse
      transportNarrow route provenanceCoarse provenanceNarrow localCert bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper coarseWindow handoff sealCoarse transportCoarse route
        provenanceCoarse localCert bundle pkg ->
      LocatedCutCarrier lower upper narrowWindow handoff sealNarrow transportNarrow route
          provenanceNarrow localCert bundle pkg ->
        UnaryHistory lower ->
          UnaryHistory upper ->
            UnaryHistory handoff ->
              UnaryHistory route ->
                UnaryHistory localCert ->
                  Cont handoff sealNarrow bridge ->
                    PkgSig bundle bridge pkg ->
                      hsame coarseWindow narrowWindow ∧
                        hsame provenanceCoarse provenanceNarrow ∧
                          UnaryHistory bridge ∧ Cont lower upper narrowWindow ∧
                            Cont handoff sealNarrow bridge ∧ PkgSig bundle bridge pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro coarseCarrier narrowCarrier lowerUnary upperUnary handoffUnary routeUnary
    localCertUnary handoffSealBridge bridgePkg
  obtain ⟨sameWindow, _sameTransport, sameProvenance, _sameSeal, _coarseWindowRoute,
    narrowWindowRoute⟩ :=
    LocatedCutCarrier_common_window_refinement coarseCarrier narrowCarrier
  obtain ⟨bridgeUnary, _sameHandoffProvenance, bridgeRoute, bridgePackage⟩ :=
    LocatedCutCarrier_standard_bridge_boundary narrowCarrier lowerUnary upperUnary
      handoffUnary routeUnary localCertUnary handoffSealBridge bridgePkg
  exact
    ⟨sameWindow, sameProvenance, bridgeUnary, narrowWindowRoute, bridgeRoute,
      bridgePackage⟩

theorem LocatedCutCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert realConsumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory provenance ->
        UnaryHistory localCert ->
          Cont sealRow provenance realConsumer ->
            PkgSig bundle realConsumer pkg ->
              hsame handoff provenance ∧ UnaryHistory realConsumer ∧
                Cont lower upper window ∧ Cont window handoff transportRow ∧
                  Cont transportRow route provenance ∧ Cont provenance localCert sealRow ∧
                    Cont sealRow provenance realConsumer ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle realConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier provenanceUnary localCertUnary sealProvenanceConsumer consumerPkg
  obtain ⟨lowerUpperWindow, windowHandoffTransport, transportRouteProvenance,
    provenanceLocalCertSeal, provenancePkg, sameSealHandoff, sameSealProvenance⟩ :=
    carrier
  have sameHandoffProvenance : hsame handoff provenance :=
    hsame_trans (hsame_symm sameSealHandoff) sameSealProvenance
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed provenanceUnary localCertUnary provenanceLocalCertSeal
  have consumerUnary : UnaryHistory realConsumer :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceConsumer
  exact
    ⟨sameHandoffProvenance, consumerUnary, lowerUpperWindow, windowHandoffTransport,
      transportRouteProvenance, provenanceLocalCertSeal, sealProvenanceConsumer, provenancePkg,
      consumerPkg⟩

theorem LocatedCutCarrier_real_seal_factorization_package [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert bridge : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          UnaryHistory handoff ->
            UnaryHistory route ->
              UnaryHistory localCert ->
                Cont handoff sealRow bridge ->
                  PkgSig bundle bridge pkg ->
                    UnaryHistory bridge ∧ hsame handoff provenance ∧ Cont lower upper window ∧
                      Cont window handoff transportRow ∧ Cont handoff sealRow bridge ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle bridge pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier lowerUnary upperUnary handoffUnary routeUnary localCertUnary handoffSealBridge
    bridgePkg
  obtain ⟨bridgeUnary, sameHandoffProvenance, bridgeRoute, bridgePackage⟩ :=
    LocatedCutCarrier_standard_bridge_boundary carrier lowerUnary upperUnary handoffUnary
      routeUnary localCertUnary handoffSealBridge bridgePkg
  obtain ⟨lowerUpperWindow, windowHandoffTransport, _transportRouteProvenance,
    _provenanceLocalCertSeal, provenancePkg, _sameSealHandoff, _sameSealProvenance⟩ :=
    carrier
  exact ⟨bridgeUnary, sameHandoffProvenance, lowerUpperWindow, windowHandoffTransport,
    bridgeRoute, provenancePkg, bridgePackage⟩

theorem LocatedCutCarrier_scoped_kernel_route [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert bridge
      realConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          UnaryHistory handoff ->
            UnaryHistory route ->
              UnaryHistory localCert ->
                Cont handoff sealRow bridge ->
                  PkgSig bundle bridge pkg ->
                    Cont sealRow provenance realConsumer ->
                      PkgSig bundle realConsumer pkg ->
                        UnaryHistory bridge ∧ UnaryHistory realConsumer ∧
                          hsame handoff provenance ∧ Cont lower upper window ∧
                            Cont window handoff transportRow ∧ Cont handoff sealRow bridge ∧
                              Cont sealRow provenance realConsumer ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle bridge pkg ∧
                                  PkgSig bundle realConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro carrier lowerUnary upperUnary handoffUnary routeUnary localCertUnary handoffSealBridge
    bridgePkg sealProvenanceConsumer consumerPkg
  obtain ⟨bridgeUnary, sameHandoffProvenance, lowerUpperWindow, windowHandoffTransport,
    bridgeRoute, provenancePkg, bridgePackage⟩ :=
    LocatedCutCarrier_real_seal_factorization_package carrier lowerUnary upperUnary
      handoffUnary routeUnary localCertUnary handoffSealBridge bridgePkg
  have exhausted :=
    LocatedCutCarrier_dyadic_interval_exhaustion carrier lowerUnary upperUnary handoffUnary
      routeUnary localCertUnary
  obtain ⟨_lowerUnary, _upperUnary, _windowUnary, _transportUnary, provenanceUnary,
    sealUnary, _lowerUpperWindow, _windowHandoffTransport, _transportRouteProvenance,
    _provenanceLocalCertSeal, _provenancePkg, _sameHandoffProvenance⟩ := exhausted
  have realConsumerUnary : UnaryHistory realConsumer :=
    unary_cont_closed sealUnary provenanceUnary sealProvenanceConsumer
  exact
    ⟨bridgeUnary, realConsumerUnary, sameHandoffProvenance, lowerUpperWindow,
      windowHandoffTransport, bridgeRoute, sealProvenanceConsumer, provenancePkg,
      bridgePackage, consumerPkg⟩

theorem LocatedCutCarrier_obligation_scope_package [AskSetup] [PackageSetup]
    {lower upper window handoff sealRow transportRow route provenance localCert bridge
      realConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg ->
      UnaryHistory lower ->
        UnaryHistory upper ->
          UnaryHistory handoff ->
            UnaryHistory route ->
              UnaryHistory localCert ->
                Cont handoff sealRow bridge ->
                  Cont sealRow provenance realConsumer ->
                    PkgSig bundle bridge pkg ->
                      PkgSig bundle realConsumer pkg ->
                        SemanticNameCert
                            (fun row : BHist =>
                              LocatedCutCarrier lower upper window handoff sealRow transportRow route
                                  provenance localCert bundle pkg ∧
                                hsame row sealRow)
                            (fun row : BHist =>
                              hsame row handoff ∨ hsame row provenance ∨ hsame row bridge ∨
                                hsame row realConsumer)
                            (fun row : BHist =>
                              PkgSig bundle provenance pkg ∧ PkgSig bundle bridge pkg ∧
                                PkgSig bundle realConsumer pkg ∧ hsame row sealRow)
                            hsame ∧
                          hsame handoff provenance ∧ UnaryHistory bridge ∧
                            UnaryHistory realConsumer ∧ Cont lower upper window ∧
                              Cont window handoff transportRow ∧
                                Cont handoff sealRow bridge ∧
                                  Cont sealRow provenance realConsumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier lowerUnary upperUnary handoffUnary routeUnary localCertUnary handoffSealBridge
    sealProvenanceConsumer bridgePkg consumerPkg
  have carrierPacket :
      LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
        bundle pkg :=
    carrier
  obtain ⟨bridgeUnary, realConsumerUnary, sameHandoffProvenance, lowerUpperWindow,
    windowHandoffTransport, bridgeRoute, consumerRoute, provenancePkg, bridgePackage,
    consumerPackage⟩ :=
    LocatedCutCarrier_scoped_kernel_route carrier lowerUnary upperUnary handoffUnary routeUnary
      localCertUnary handoffSealBridge bridgePkg sealProvenanceConsumer consumerPkg
  obtain ⟨_lowerUpperWindow, _windowHandoffTransport, _transportRouteProvenance,
    _provenanceLocalCertSeal, _provenancePkg, sameSealHandoff, _sameSealProvenance⟩ :=
    carrier
  have sourceSeal :
      (fun row : BHist =>
        LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance localCert
            bundle pkg ∧
          hsame row sealRow) sealRow := by
    exact ⟨carrierPacket, hsame_refl sealRow⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            LocatedCutCarrier lower upper window handoff sealRow transportRow route provenance
                localCert bundle pkg ∧
              hsame row sealRow)
          (fun row : BHist =>
            hsame row handoff ∨ hsame row provenance ∨ hsame row bridge ∨
              hsame row realConsumer)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle bridge pkg ∧
              PkgSig bundle realConsumer pkg ∧ hsame row sealRow)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow sourceSeal
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
        intro _row _other sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact Or.inl (hsame_trans source.right sameSealHandoff)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, bridgePackage, consumerPackage, source.right⟩
  }
  exact
    ⟨cert, sameHandoffProvenance, bridgeUnary, realConsumerUnary, lowerUpperWindow,
      windowHandoffTransport, bridgeRoute, consumerRoute⟩

end BEDC.Derived.LocatedCutUp
