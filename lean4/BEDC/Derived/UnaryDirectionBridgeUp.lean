import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UnaryDirectionBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UnaryDirectionBridgeCarrier [AskSetup] [PackageSetup]
    (natRow axisRow bridge kernel boundary ledger transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory natRow ∧ UnaryHistory axisRow ∧ UnaryHistory bridge ∧
    UnaryHistory kernel ∧ UnaryHistory boundary ∧ UnaryHistory ledger ∧
      UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont natRow axisRow bridge ∧ Cont bridge kernel boundary ∧
          Cont boundary ledger transports ∧ Cont transports routes provenance ∧
            Cont routes provenance name ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg

theorem UnaryDirectionBridgeCarrier_kernel_distinct_obligations [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      UnaryHistory natRow ∧ UnaryHistory axisRow ∧ UnaryHistory bridge ∧
        UnaryHistory kernel ∧ UnaryHistory boundary ∧
          Cont natRow axisRow bridge ∧ Cont bridge kernel boundary ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
              SemanticNameCert
                (fun row : BHist =>
                  UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger
                      transports routes provenance name bundle pkg ∧
                    hsame row name)
                (fun row : BHist =>
                  UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger
                      transports routes provenance name bundle pkg ∧
                    hsame row name)
                (fun row : BHist =>
                  UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger
                      transports routes provenance name bundle pkg ∧
                    hsame row name)
                hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier
  have carrierWitness :
      UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg := carrier
  obtain ⟨natUnary, axisUnary, bridgeUnary, kernelUnary, boundaryUnary, _ledgerUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, natAxisBridge,
    bridgeKernelBoundary, _boundaryLedgerTransports, _transportsRoutesProvenance,
    _routesProvenanceName, provenancePkg, namePkg⟩ := carrier
  have nameCert :
      SemanticNameCert
        (fun row : BHist =>
          UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports
              routes provenance name bundle pkg ∧
            hsame row name)
        (fun row : BHist =>
          UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports
              routes provenance name bundle pkg ∧
            hsame row name)
        (fun row : BHist =>
          UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports
              routes provenance name bundle pkg ∧
            hsame row name)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro name (And.intro carrierWitness (hsame_refl name))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨natUnary, axisUnary, bridgeUnary, kernelUnary, boundaryUnary, natAxisBridge,
      bridgeKernelBoundary, provenancePkg, namePkg, nameCert⟩

theorem UnaryDirectionBridgeCarrier_standard_boundary_readout [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name
      boundaryRead additiveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      Cont boundary ledger boundaryRead ->
        Cont boundaryRead routes additiveRead ->
          PkgSig bundle boundaryRead pkg ->
            PkgSig bundle additiveRead pkg ->
              UnaryHistory boundaryRead ∧ UnaryHistory additiveRead ∧
                Cont bridge kernel boundary ∧ Cont boundary ledger transports ∧
                  Cont boundary ledger boundaryRead ∧ Cont boundaryRead routes additiveRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg ∧
                      PkgSig bundle additiveRead pkg := by
  intro carrier boundaryLedgerRead readRoutesAdditive boundaryReadPkg additiveReadPkg
  obtain ⟨_natUnary, _axisUnary, _bridgeUnary, _kernelUnary, boundaryUnary, ledgerUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _natAxisBridge,
    bridgeKernelBoundary, boundaryLedgerTransports, _transportsRoutesProvenance,
    _routesProvenanceName, provenancePkg, _namePkg⟩ := carrier
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary ledgerUnary boundaryLedgerRead
  have additiveReadUnary : UnaryHistory additiveRead :=
    unary_cont_closed boundaryReadUnary routesUnary readRoutesAdditive
  exact
    ⟨boundaryReadUnary, additiveReadUnary, bridgeKernelBoundary, boundaryLedgerTransports,
      boundaryLedgerRead, readRoutesAdditive, provenancePkg, boundaryReadPkg, additiveReadPkg⟩

theorem UnaryDirectionBridgeCarrier_source_obligation_inventory [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name
      sourceRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      Cont natRow axisRow sourceRead ->
        Cont boundary ledger boundaryRead ->
          PkgSig bundle sourceRead pkg ->
            PkgSig bundle boundaryRead pkg ->
              UnaryHistory natRow /\ UnaryHistory axisRow /\ UnaryHistory sourceRead /\
                UnaryHistory boundaryRead /\ Cont natRow axisRow bridge /\
                  Cont natRow axisRow sourceRead /\ Cont bridge kernel boundary /\
                    Cont boundary ledger boundaryRead /\ PkgSig bundle provenance pkg /\
                      PkgSig bundle name pkg /\ PkgSig bundle sourceRead pkg /\
                        PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier natAxisSource boundaryLedgerRead sourceReadPkg boundaryReadPkg
  obtain ⟨natUnary, axisUnary, _bridgeUnary, _kernelUnary, boundaryUnary, ledgerUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, natAxisBridge,
    bridgeKernelBoundary, _boundaryLedgerTransports, _transportsRoutesProvenance,
    _routesProvenanceName, provenancePkg, namePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed natUnary axisUnary natAxisSource
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary ledgerUnary boundaryLedgerRead
  exact
    ⟨natUnary, axisUnary, sourceReadUnary, boundaryReadUnary, natAxisBridge,
      natAxisSource, bridgeKernelBoundary, boundaryLedgerRead, provenancePkg, namePkg,
      sourceReadPkg, boundaryReadPkg⟩

theorem UnaryDirectionBridgeCarrier_source_classifier_transport [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name
      natRow' axisRow' bridge' kernel' boundary' ledger' transports' routes'
      provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      hsame natRow natRow' ->
        hsame axisRow axisRow' ->
          hsame bridge bridge' ->
            hsame kernel kernel' ->
              hsame boundary boundary' ->
                hsame ledger ledger' ->
                  hsame transports transports' ->
                    hsame routes routes' ->
                      hsame provenance provenance' ->
                        hsame name name' ->
                          UnaryDirectionBridgeCarrier natRow' axisRow' bridge' kernel'
                            boundary' ledger' transports' routes' provenance' name'
                            bundle pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig hsame
  intro carrier sameNat sameAxis sameBridge sameKernel sameBoundary sameLedger
    sameTransports sameRoutes sameProvenance sameName
  cases sameNat
  cases sameAxis
  cases sameBridge
  cases sameKernel
  cases sameBoundary
  cases sameLedger
  cases sameTransports
  cases sameRoutes
  cases sameProvenance
  cases sameName
  exact carrier

theorem UnaryDirectionBridgeCarrier_classifier_stability [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name natRow'
      axisRow' bridge' kernel' boundary' ledger' transports' routes' provenance' name'
      boundaryRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      hsame natRow natRow' ->
        hsame axisRow axisRow' ->
          hsame bridge bridge' ->
            hsame kernel kernel' ->
              hsame boundary boundary' ->
                hsame ledger ledger' ->
                  hsame transports transports' ->
                    hsame routes routes' ->
                      hsame provenance provenance' ->
                        hsame name name' ->
                          Cont boundary' ledger' boundaryRead' ->
                            PkgSig bundle boundaryRead' pkg ->
                              UnaryDirectionBridgeCarrier natRow' axisRow' bridge' kernel'
                                  boundary' ledger' transports' routes' provenance' name'
                                  bundle pkg ∧
                                UnaryHistory boundaryRead' ∧ Cont bridge' kernel' boundary' ∧
                                  Cont boundary' ledger' boundaryRead' ∧
                                    PkgSig bundle provenance' pkg ∧
                                      PkgSig bundle name' pkg ∧
                                        PkgSig bundle boundaryRead' pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  intro carrier sameNat sameAxis sameBridge sameKernel sameBoundary sameLedger
    sameTransports sameRoutes sameProvenance sameName boundaryLedgerRead boundaryReadPkg
  have transported :
      UnaryDirectionBridgeCarrier natRow' axisRow' bridge' kernel' boundary' ledger'
        transports' routes' provenance' name' bundle pkg :=
    UnaryDirectionBridgeCarrier_source_classifier_transport (pkg := pkg) carrier sameNat
      sameAxis sameBridge sameKernel sameBoundary sameLedger sameTransports sameRoutes
      sameProvenance sameName
  have transportedCarrier :
      UnaryDirectionBridgeCarrier natRow' axisRow' bridge' kernel' boundary' ledger'
        transports' routes' provenance' name' bundle pkg := transported
  obtain ⟨_natUnary, _axisUnary, _bridgeUnary, _kernelUnary, boundaryUnary, ledgerUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _natAxisBridge,
    bridgeKernelBoundary, _boundaryLedgerTransports, _transportsRoutesProvenance,
    _routesProvenanceName, provenancePkg, namePkg⟩ := transported
  have boundaryReadUnary : UnaryHistory boundaryRead' :=
    unary_cont_closed boundaryUnary ledgerUnary boundaryLedgerRead
  exact
    ⟨transportedCarrier, boundaryReadUnary, bridgeKernelBoundary, boundaryLedgerRead,
      provenancePkg, namePkg, boundaryReadPkg⟩

theorem UnaryDirectionBridgeCarrier_ledger_policy [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      Cont ledger transports ledgerRead ->
        PkgSig bundle ledgerRead pkg ->
          UnaryHistory natRow /\ UnaryHistory axisRow /\ UnaryHistory bridge /\
            UnaryHistory kernel /\ UnaryHistory boundary /\ UnaryHistory ledger /\
              UnaryHistory transports /\ UnaryHistory ledgerRead /\
                Cont natRow axisRow bridge /\ Cont bridge kernel boundary /\
                  Cont boundary ledger transports /\ Cont ledger transports ledgerRead /\
                    PkgSig bundle provenance pkg /\ PkgSig bundle name pkg /\
                      PkgSig bundle ledgerRead pkg := by
  intro carrier ledgerTransportRead ledgerReadPkg
  obtain ⟨natUnary, axisUnary, bridgeUnary, kernelUnary, boundaryUnary, ledgerUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, natAxisBridge,
    bridgeKernelBoundary, boundaryLedgerTransports, _transportsRoutesProvenance,
    _routesProvenanceName, provenancePkg, namePkg⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary transportsUnary ledgerTransportRead
  exact
    ⟨natUnary, axisUnary, bridgeUnary, kernelUnary, boundaryUnary, ledgerUnary,
      transportsUnary, ledgerReadUnary, natAxisBridge, bridgeKernelBoundary,
      boundaryLedgerTransports, ledgerTransportRead, provenancePkg, namePkg, ledgerReadPkg⟩

theorem UnaryDirectionBridgeCarrier_additive_consumer_exactness [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name handoff
      additiveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      Cont boundary ledger handoff ->
        Cont handoff routes additiveRead ->
          PkgSig bundle handoff pkg ->
            PkgSig bundle additiveRead pkg ->
              UnaryHistory natRow ∧ UnaryHistory axisRow ∧ UnaryHistory bridge ∧
                UnaryHistory kernel ∧ UnaryHistory boundary ∧ UnaryHistory ledger ∧
                  UnaryHistory transports ∧ UnaryHistory handoff ∧ UnaryHistory additiveRead ∧
                    Cont natRow axisRow bridge ∧ Cont bridge kernel boundary ∧
                      Cont boundary ledger transports ∧ Cont boundary ledger handoff ∧
                        Cont handoff routes additiveRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle handoff pkg ∧
                            PkgSig bundle additiveRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier boundaryLedgerHandoff handoffRoutesAdditive handoffPkg additiveReadPkg
  obtain ⟨natUnary, axisUnary, bridgeUnary, kernelUnary, boundaryUnary, ledgerUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, natAxisBridge,
    bridgeKernelBoundary, boundaryLedgerTransports, _transportsRoutesProvenance,
    _routesProvenanceName, provenancePkg, namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed boundaryUnary ledgerUnary boundaryLedgerHandoff
  have additiveReadUnary : UnaryHistory additiveRead :=
    unary_cont_closed handoffUnary routesUnary handoffRoutesAdditive
  exact
    ⟨natUnary, axisUnary, bridgeUnary, kernelUnary, boundaryUnary, ledgerUnary,
      transportsUnary, handoffUnary, additiveReadUnary, natAxisBridge, bridgeKernelBoundary,
      boundaryLedgerTransports, boundaryLedgerHandoff, handoffRoutesAdditive, provenancePkg,
      namePkg, handoffPkg, additiveReadPkg⟩

theorem UnaryDirectionBridgeCarrier_empty_intersection_readback [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name
      kernelRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      Cont bridge kernel boundary ->
        Cont kernel boundary kernelRead ->
          PkgSig bundle kernelRead pkg ->
            UnaryHistory kernel ∧ UnaryHistory boundary ∧ UnaryHistory kernelRead ∧
              Cont bridge kernel boundary ∧ Cont kernel boundary kernelRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle kernelRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier displayedBoundary kernelBoundaryRead kernelReadPkg
  obtain ⟨_natUnary, _axisUnary, _bridgeUnary, kernelUnary, boundaryUnary, _ledgerUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _natAxisBridge,
    _bridgeKernelBoundary, _boundaryLedgerTransports, _transportsRoutesProvenance,
    _routesProvenanceName, provenancePkg, namePkg⟩ := carrier
  have kernelReadUnary : UnaryHistory kernelRead :=
    unary_cont_closed kernelUnary boundaryUnary kernelBoundaryRead
  exact
    ⟨kernelUnary, boundaryUnary, kernelReadUnary, displayedBoundary, kernelBoundaryRead,
      provenancePkg, namePkg, kernelReadPkg⟩

theorem UnaryDirectionBridgeCarrier_namecert_scoped_package [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name
      boundaryRead additiveRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      Cont boundary ledger boundaryRead ->
        Cont boundaryRead routes additiveRead ->
          Cont ledger transports ledgerRead ->
            PkgSig bundle boundaryRead pkg ->
              PkgSig bundle additiveRead pkg ->
                PkgSig bundle ledgerRead pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary
                            ledger transports routes provenance name bundle pkg ∧
                          hsame row name)
                      (fun row : BHist =>
                        UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary
                            ledger transports routes provenance name bundle pkg ∧
                          hsame row name)
                      (fun row : BHist =>
                        UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary
                            ledger transports routes provenance name bundle pkg ∧
                          hsame row name)
                      hsame ∧
                    UnaryHistory additiveRead ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert UnaryDirectionBridgeCarrier
  intro carrier boundaryLedgerRead readRoutesAdditive ledgerTransportRead boundaryReadPkg
    additiveReadPkg ledgerReadPkg
  have kernelObligations :=
    UnaryDirectionBridgeCarrier_kernel_distinct_obligations (pkg := pkg) carrier
  have boundaryReadout :=
    UnaryDirectionBridgeCarrier_standard_boundary_readout (pkg := pkg) carrier boundaryLedgerRead
      readRoutesAdditive boundaryReadPkg additiveReadPkg
  have ledgerPolicy :=
    UnaryDirectionBridgeCarrier_ledger_policy (pkg := pkg) carrier ledgerTransportRead ledgerReadPkg
  have nameCert :
      SemanticNameCert
        (fun row : BHist =>
          UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports
              routes provenance name bundle pkg ∧
            hsame row name)
        (fun row : BHist =>
          UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports
              routes provenance name bundle pkg ∧
            hsame row name)
        (fun row : BHist =>
          UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports
              routes provenance name bundle pkg ∧
            hsame row name)
        hsame :=
    kernelObligations.right.right.right.right.right.right.right.right.right
  have additiveUnary : UnaryHistory additiveRead :=
    boundaryReadout.right.left
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    ledgerPolicy.right.right.right.right.right.right.right.left
  exact ⟨nameCert, additiveUnary, ledgerReadUnary⟩

theorem UnaryDirectionBridgeCarrier_consumer_normal_form [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      (Cont ledger transports consumer ∨ Cont transports routes consumer ∨
          Cont routes provenance consumer) ->
        PkgSig bundle consumer pkg ->
          UnaryHistory consumer ∧ UnaryHistory natRow ∧ UnaryHistory axisRow ∧
            UnaryHistory bridge ∧ UnaryHistory kernel ∧ UnaryHistory boundary ∧
              UnaryHistory ledger ∧ UnaryHistory transports ∧ UnaryHistory routes ∧
                Cont natRow axisRow bridge ∧ Cont bridge kernel boundary ∧
                  (Cont ledger transports consumer ∨ Cont transports routes consumer ∨
                    Cont routes provenance consumer) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier consumerRoute consumerPkg
  obtain ⟨natUnary, axisUnary, bridgeUnary, kernelUnary, boundaryUnary, ledgerUnary,
    transportsUnary, routesUnary, provenanceUnary, _nameUnary, natAxisBridge,
    bridgeKernelBoundary, _boundaryLedgerTransports, _transportsRoutesProvenance,
    _routesProvenanceName, provenancePkg, namePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer := by
    cases consumerRoute with
    | inl ledgerTransportsConsumer =>
        exact unary_cont_closed ledgerUnary transportsUnary ledgerTransportsConsumer
    | inr rest =>
        cases rest with
        | inl transportsRoutesConsumer =>
            exact unary_cont_closed transportsUnary routesUnary transportsRoutesConsumer
        | inr routesProvenanceConsumer =>
            exact unary_cont_closed routesUnary provenanceUnary routesProvenanceConsumer
  exact
    ⟨consumerUnary, natUnary, axisUnary, bridgeUnary, kernelUnary, boundaryUnary, ledgerUnary,
      transportsUnary, routesUnary, natAxisBridge, bridgeKernelBoundary, consumerRoute,
      provenancePkg, namePkg, consumerPkg⟩

theorem UnaryDirectionBridgeCarrier_kernel_axis_composition [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name kernelAxis
      axisAdd : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      Cont kernel axisRow kernelAxis ->
        Cont kernelAxis bridge axisAdd ->
          PkgSig bundle kernelAxis pkg ->
            PkgSig bundle axisAdd pkg ->
              UnaryHistory kernel ∧ UnaryHistory axisRow ∧ UnaryHistory kernelAxis ∧
                UnaryHistory axisAdd ∧ Cont natRow axisRow bridge ∧
                  Cont bridge kernel boundary ∧ Cont kernel axisRow kernelAxis ∧
                    Cont kernelAxis bridge axisAdd ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle kernelAxis pkg ∧
                        PkgSig bundle axisAdd pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier kernelAxisCont axisAddCont kernelAxisPkg axisAddPkg
  obtain ⟨_natUnary, axisUnary, bridgeUnary, kernelUnary, _boundaryUnary, _ledgerUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, natAxisBridge,
    bridgeKernelBoundary, _boundaryLedgerTransports, _transportsRoutesProvenance,
    _routesProvenanceName, provenancePkg, namePkg⟩ := carrier
  have kernelAxisUnary : UnaryHistory kernelAxis :=
    unary_cont_closed kernelUnary axisUnary kernelAxisCont
  have axisAddUnary : UnaryHistory axisAdd :=
    unary_cont_closed kernelAxisUnary bridgeUnary axisAddCont
  exact
    ⟨kernelUnary, axisUnary, kernelAxisUnary, axisAddUnary, natAxisBridge,
      bridgeKernelBoundary, kernelAxisCont, axisAddCont, provenancePkg, namePkg,
      kernelAxisPkg, axisAddPkg⟩

theorem UnaryDirectionBridgeCarrier_standard_boundary_consumer_factorization
    [AskSetup] [PackageSetup]
    {natRow axisRow bridge kernel boundary ledger transports routes provenance name boundaryRead
      additiveRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryDirectionBridgeCarrier natRow axisRow bridge kernel boundary ledger transports routes
        provenance name bundle pkg ->
      Cont boundary ledger boundaryRead ->
        Cont boundaryRead routes additiveRead ->
          Cont ledger transports ledgerRead ->
            PkgSig bundle boundaryRead pkg ->
              PkgSig bundle additiveRead pkg ->
                PkgSig bundle ledgerRead pkg ->
                  UnaryHistory natRow ∧ UnaryHistory axisRow ∧ UnaryHistory boundaryRead ∧
                    UnaryHistory additiveRead ∧ UnaryHistory ledgerRead ∧
                      Cont natRow axisRow bridge ∧ Cont bridge kernel boundary ∧
                        Cont boundary ledger boundaryRead ∧
                          Cont boundaryRead routes additiveRead ∧
                            Cont ledger transports ledgerRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                                PkgSig bundle additiveRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier boundaryLedgerRead readRoutesAdditive ledgerTransportRead _boundaryReadPkg
    additiveReadPkg _ledgerReadPkg
  obtain ⟨natUnary, axisUnary, _bridgeUnary, _kernelUnary, boundaryUnary, ledgerUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, natAxisBridge,
    bridgeKernelBoundary, _boundaryLedgerTransports, _transportsRoutesProvenance,
    _routesProvenanceName, provenancePkg, namePkg⟩ := carrier
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryUnary ledgerUnary boundaryLedgerRead
  have additiveReadUnary : UnaryHistory additiveRead :=
    unary_cont_closed boundaryReadUnary routesUnary readRoutesAdditive
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary transportsUnary ledgerTransportRead
  exact
    ⟨natUnary, axisUnary, boundaryReadUnary, additiveReadUnary, ledgerReadUnary,
      natAxisBridge, bridgeKernelBoundary, boundaryLedgerRead, readRoutesAdditive,
      ledgerTransportRead, provenancePkg, namePkg, additiveReadPkg⟩

end BEDC.Derived.UnaryDirectionBridgeUp
