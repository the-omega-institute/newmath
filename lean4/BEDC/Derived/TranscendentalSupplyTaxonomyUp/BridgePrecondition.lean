import BEDC.Derived.TranscendentalSupplyTaxonomyUp.NameCertObligations

namespace BEDC.Derived.TranscendentalSupplyTaxonomyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TranscendentalSupplyTaxonomyCarrier_bridge_precondition [AskSetup] [PackageSetup]
    {socketKind requestedSupply gap auditGate site transport route provenance nameRow
      auditRead boundary bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TranscendentalSupplyTaxonomyCarrier socketKind requestedSupply gap auditGate site transport
        route provenance nameRow bundle pkg ->
      Cont gap auditGate auditRead ->
        Cont auditRead site boundary ->
          Cont boundary transport bridgeRead ->
            PkgSig bundle bridgeRead pkg ->
              UnaryHistory socketKind ∧ UnaryHistory requestedSupply ∧ UnaryHistory gap ∧
                UnaryHistory auditGate ∧ UnaryHistory auditRead ∧ UnaryHistory boundary ∧
                  UnaryHistory bridgeRead ∧ Cont socketKind requestedSupply gap ∧
                    Cont gap auditGate auditRead ∧ Cont auditRead site boundary ∧
                      Cont boundary transport bridgeRead ∧ hsame site (append gap auditGate) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier gapAuditRead auditReadSiteBoundary boundaryTransportBridge bridgePkg
  rcases carrier with
    ⟨socketKindUnary, requestedSupplyUnary, gapUnary, auditGateUnary, siteUnary,
      transportUnary, _routeUnary, _provenanceUnary, _nameRowUnary, socketRequestedGap,
      _gapAuditSite, _siteTransportRoute, _routeProvenanceName, siteSameGapAudit,
      provenancePkg⟩
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed gapUnary auditGateUnary gapAuditRead
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed auditReadUnary siteUnary auditReadSiteBoundary
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed boundaryUnary transportUnary boundaryTransportBridge
  exact
    ⟨socketKindUnary, requestedSupplyUnary, gapUnary, auditGateUnary, auditReadUnary,
      boundaryUnary, bridgeReadUnary, socketRequestedGap, gapAuditRead, auditReadSiteBoundary,
      boundaryTransportBridge, siteSameGapAudit, provenancePkg, bridgePkg⟩

theorem TranscendentalSupplyTaxonomySocket_ledger_readback [AskSetup] [PackageSetup]
    {socketKind requestedSupply gap auditGate site transport route provenance nameRow auditRead
      boundary ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TranscendentalSupplyTaxonomyCarrier socketKind requestedSupply gap auditGate site transport
        route provenance nameRow bundle pkg →
      Cont gap auditGate auditRead →
        Cont auditRead site boundary →
          Cont boundary route ledgerRead →
            PkgSig bundle ledgerRead pkg →
              UnaryHistory socketKind ∧ UnaryHistory requestedSupply ∧ UnaryHistory gap ∧
                UnaryHistory auditGate ∧ UnaryHistory site ∧ UnaryHistory auditRead ∧
                  UnaryHistory boundary ∧ UnaryHistory ledgerRead ∧
                    Cont socketKind requestedSupply gap ∧ Cont gap auditGate auditRead ∧
                      Cont auditRead site boundary ∧ Cont boundary route ledgerRead ∧
                        hsame site (append gap auditGate) ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier gapAuditRead auditReadSiteBoundary boundaryRouteLedger ledgerPkg
  rcases carrier with
    ⟨socketKindUnary, requestedSupplyUnary, gapUnary, auditGateUnary, siteUnary,
      _transportUnary, routeUnary, _provenanceUnary, _nameRowUnary, socketRequestedGap,
      _gapAuditSite, _siteTransportRoute, _routeProvenanceName, siteSameGapAudit,
      provenancePkg⟩
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed gapUnary auditGateUnary gapAuditRead
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed auditReadUnary siteUnary auditReadSiteBoundary
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundaryUnary routeUnary boundaryRouteLedger
  exact
    ⟨socketKindUnary, requestedSupplyUnary, gapUnary, auditGateUnary, siteUnary,
      auditReadUnary, boundaryUnary, ledgerReadUnary, socketRequestedGap, gapAuditRead,
      auditReadSiteBoundary, boundaryRouteLedger, siteSameGapAudit, provenancePkg,
      ledgerPkg⟩

end BEDC.Derived.TranscendentalSupplyTaxonomyUp
