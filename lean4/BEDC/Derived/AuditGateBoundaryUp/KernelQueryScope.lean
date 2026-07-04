import BEDC.Derived.AuditGateBoundaryUp
import BEDC.Derived.HostDelegationSocketUp

namespace BEDC.Derived.AuditGateBoundaryUp

open BEDC.Derived.HostDelegationSocketUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuditGateBoundaryCarrier_kernel_query_scope [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert sourceConsumer dependencyConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      Cont sourceScan transport sourceConsumer ->
        Cont dependencyReport route dependencyConsumer ->
          PkgSig bundle sourceConsumer pkg ->
            PkgSig bundle dependencyConsumer pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row sourceConsumer ∨ hsame row dependencyConsumer) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row sourceScan ∨ hsame row dependencyReport ∨
                      hsame row sourceConsumer ∨ hsame row dependencyConsumer)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle sourceConsumer pkg ∧
                      PkgSig bundle dependencyConsumer pkg)
                  hsame ∧
                UnaryHistory sourceConsumer ∧ UnaryHistory dependencyConsumer ∧
                  Cont sourceScan transport sourceConsumer ∧
                    Cont dependencyReport route dependencyConsumer := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier sourceRoute dependencyRoute sourcePkg dependencyPkg
  obtain ⟨sourceUnary, dependencyUnary, _markerUnary, _originUnary, transportUnary,
    routeUnary, _provenanceUnary, _gapUnary, _nameUnary, _dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, _provenancePkg, _namePkg⟩ := carrier
  have sourceConsumerUnary : UnaryHistory sourceConsumer :=
    unary_cont_closed sourceUnary transportUnary sourceRoute
  have dependencyConsumerUnary : UnaryHistory dependencyConsumer :=
    unary_cont_closed dependencyUnary routeUnary dependencyRoute
  have sourceConsumerSource :
      (fun row : BHist =>
        (hsame row sourceConsumer ∨ hsame row dependencyConsumer) ∧ UnaryHistory row)
        sourceConsumer := by
    exact ⟨Or.inl (hsame_refl sourceConsumer), sourceConsumerUnary⟩
  have core :
      NameCert
        (fun row : BHist =>
          (hsame row sourceConsumer ∨ hsame row dependencyConsumer) ∧ UnaryHistory row)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro sourceConsumer sourceConsumerSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have otherChoice : hsame other sourceConsumer ∨ hsame other dependencyConsumer := by
          cases sourceRow.left with
          | inl sameSource =>
              exact Or.inl (hsame_trans (hsame_symm same) sameSource)
          | inr sameDependency =>
              exact Or.inr (hsame_trans (hsame_symm same) sameDependency)
        have otherUnary : UnaryHistory other :=
          unary_transport sourceRow.right same
        exact ⟨otherChoice, otherUnary⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sourceConsumer ∨ hsame row dependencyConsumer) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceScan ∨ hsame row dependencyReport ∨
              hsame row sourceConsumer ∨ hsame row dependencyConsumer)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle sourceConsumer pkg ∧
              PkgSig bundle dependencyConsumer pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row sourceRow
        cases sourceRow.left with
        | inl sameSource =>
            exact Or.inr (Or.inr (Or.inl sameSource))
        | inr sameDependency =>
            exact Or.inr (Or.inr (Or.inr sameDependency))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, sourcePkg, dependencyPkg⟩
    }
  exact
    ⟨cert, sourceConsumerUnary, dependencyConsumerUnary, sourceRoute, dependencyRoute⟩

theorem AuditGateBoundaryCarrier_host_delegation_audit_query_handoff [AskSetup]
    [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert marker audit kernel target socketTransport continuation socketProvenance
      socketLedger socketName marker' audit' kernel' target' socketTransport' continuation'
      socketProvenance' socketLedger' socketName' auditEvidence kernelEvidence gateConsumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      hostDelegationSocketToEventFlow
          (HostDelegationSocketUp.mk marker audit kernel target socketTransport continuation
            socketProvenance socketLedger socketName) =
        hostDelegationSocketToEventFlow
          (HostDelegationSocketUp.mk marker' audit' kernel' target' socketTransport'
            continuation' socketProvenance' socketLedger' socketName') ->
        Cont audit socketTransport auditEvidence ->
          Cont kernel target kernelEvidence ->
            Cont markerResolution originLedger gateConsumer ->
              PkgSig bundle socketProvenance pkg ->
                PkgSig bundle gateConsumer pkg ->
                  hsame audit audit' ∧ hsame kernel kernel' ∧
                    Cont audit' socketTransport' auditEvidence ∧
                      Cont kernel' target' kernelEvidence ∧
                        UnaryHistory markerResolution ∧
                          Cont markerResolution originLedger gateConsumer ∧
                            PkgSig bundle gateConsumer pkg ∧
                              PkgSig bundle socketProvenance' pkg := by
  -- BEDC touchpoint anchor: HostDelegationSocket_audit_face_separation BHist Cont PkgSig
  intro carrier encodedSame auditRoute kernelRoute gateRoute socketPkg gatePkg
  obtain ⟨_sourceUnary, _dependencyUnary, markerUnary, _originUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _gapUnary, _nameUnary, _dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, _provenancePkg, _namePkg⟩ := carrier
  have socketRows :=
    HostDelegationSocket_audit_face_separation
      (marker := marker) (audit := audit) (kernel := kernel) (target := target)
      (transport := socketTransport) (continuation := continuation)
      (provenance := socketProvenance) (ledger := socketLedger) (name := socketName)
      (marker' := marker') (audit' := audit') (kernel' := kernel') (target' := target')
      (transport' := socketTransport') (continuation' := continuation')
      (provenance' := socketProvenance') (ledger' := socketLedger')
      (name' := socketName') (auditEvidence := auditEvidence)
      (kernelEvidence := kernelEvidence) encodedSame auditRoute kernelRoute socketPkg
  exact
    ⟨socketRows.left, socketRows.right.left, socketRows.right.right.left,
      socketRows.right.right.right.left, markerUnary, gateRoute, gatePkg,
      socketRows.right.right.right.right⟩

theorem AuditGateBoundaryCarrier_host_delegation_namecert_query_handoff [AskSetup]
    [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert marker audit kernel target socketTransport continuation socketProvenance
      socketLedger socketName gateConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      HostDelegationSocketCarrier marker audit kernel target socketTransport continuation
        socketProvenance socketLedger socketName bundle pkg ->
        Cont markerResolution originLedger gateConsumer ->
          PkgSig bundle gateConsumer pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  HostDelegationSocketCarrier marker audit kernel target socketTransport
                    continuation socketProvenance socketLedger socketName bundle pkg ∧
                    hsame row socketName)
                (fun row : BHist =>
                  Cont marker target socketLedger ∧
                    Cont socketLedger socketName continuation ∧ hsame row socketName)
                (fun row : BHist => PkgSig bundle socketName pkg ∧ hsame row socketName)
                hsame ∧
              Cont marker target socketLedger ∧
                Cont socketLedger socketName continuation ∧
                  PkgSig bundle socketName pkg ∧
                    UnaryHistory markerResolution ∧
                      Cont markerResolution originLedger gateConsumer ∧
                        PkgSig bundle gateConsumer pkg := by
  -- BEDC touchpoint anchor: HostDelegationSocketCarrier_semantic_name_certificate BHist Cont
  intro carrier socketCarrier gateRoute gatePkg
  obtain ⟨_sourceUnary, _dependencyUnary, markerUnary, _originUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _gapUnary, _nameUnary, _dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, _provenancePkg, _namePkg⟩ := carrier
  have socketCert :=
    HostDelegationSocketCarrier_semantic_name_certificate
      (marker := marker) (audit := audit) (kernel := kernel) (target := target)
      (transport := socketTransport) (continuation := continuation)
      (provenance := socketProvenance) (ledger := socketLedger) (name := socketName)
      (bundle := bundle) (pkg := pkg) socketCarrier
  have socketSource :
      HostDelegationSocketCarrier marker audit kernel target socketTransport continuation
          socketProvenance socketLedger socketName bundle pkg ∧
        hsame socketName socketName := by
    exact ⟨socketCarrier, hsame_refl socketName⟩
  have hostPattern := socketCert.pattern_sound socketSource
  have hostLedger := socketCert.ledger_sound socketSource
  exact
    ⟨socketCert, hostPattern.left, hostPattern.right.left, hostLedger.left, markerUnary,
      gateRoute, gatePkg⟩

end BEDC.Derived.AuditGateBoundaryUp
