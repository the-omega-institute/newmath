import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ApophaticNameCarrier [AskSetup] [PackageSetup]
    (socket request gate ledger transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
    UnaryHistory ledger ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont socket request gate ∧
        Cont request gate route ∧ Cont gate ledger route ∧ Cont gate ledger nameRow ∧
          hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg

theorem ApophaticNameCarrier_refusal_ledger_surface [AskSetup] [PackageSetup]
    {socket request refusal ledger sameRows routes provenance nameCert consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request refusal ledger sameRows routes provenance nameCert
        bundle pkg ->
      Cont ledger nameCert consumerRead ->
        UnaryHistory consumerRead ∧ UnaryHistory ledger ∧
          hsame ledger (append request refusal) ∧ PkgSig bundle provenance pkg := by
  intro carrier consumerRoute
  obtain ⟨_socketUnary, _requestUnary, _refusalUnary, ledgerUnary, _sameRowsUnary,
    _routesUnary, _provenanceUnary, nameCertUnary, _socketRequestRefusal,
    _requestRefusalRoutes, _refusalLedgerRoutes, _refusalLedgerNameCert, ledgerSameRequestRefusal,
    provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerUnary nameCertUnary consumerRoute
  exact ⟨consumerUnary, ledgerUnary, ledgerSameRequestRefusal, provenancePkg⟩

theorem ApophaticNameCarrier_refusal_ledger [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      Cont ledger route exported ->
        PkgSig bundle exported pkg ->
          UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
            UnaryHistory ledger ∧ UnaryHistory exported ∧ Cont socket request gate ∧
              Cont gate ledger route ∧ Cont ledger route exported ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle exported pkg := by
  intro carrier ledgerRouteExported exportedPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute,
    gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed gateUnary ledgerUnary gateLedgerRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed ledgerUnary routeUnary ledgerRouteExported
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, exportedUnary, socketRequestGate,
      gateLedgerRoute, ledgerRouteExported, provenancePkg, exportedPkg⟩

theorem ApophaticNameCarrier_obligation_surface [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg →
      Cont ledger nameRow auditRead →
        PkgSig bundle auditRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row nameRow ∧
                  ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                    bundle pkg)
              (fun row : BHist => hsame row nameRow)
              (fun row : BHist => hsame row nameRow ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory socket ∧
            UnaryHistory request ∧
            UnaryHistory gate ∧
            UnaryHistory ledger ∧
            UnaryHistory nameRow ∧
            UnaryHistory auditRead ∧
            Cont socket request gate ∧
            Cont gate ledger nameRow ∧
            Cont ledger nameRow auditRead ∧
            PkgSig bundle provenance pkg ∧
            PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameAudit auditPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameAudit
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row nameRow ∧
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg)
        (fun row : BHist => hsame row nameRow)
        (fun row : BHist => hsame row nameRow ∧ PkgSig bundle provenance pkg)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro nameRow (And.intro (hsame_refl nameRow) carrierPacket)
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
    · intro row source
      exact source.left
    · intro row source
      exact And.intro source.left provenancePkg
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, nameRowUnary, auditUnary,
      socketRequestGate, gateLedgerNameRow, ledgerNameAudit, provenancePkg, auditPkg⟩

theorem ApophaticNameCarrier_refusal_transport_totality [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socket' request' gate'
      ledger' transport' route' provenance' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      hsame socket socket' →
        hsame request request' →
          hsame gate gate' →
            hsame ledger ledger' →
              hsame transport transport' →
                hsame route route' →
                  hsame provenance provenance' →
                    hsame nameRow nameRow' →
                      PkgSig bundle provenance' pkg →
                        ApophaticNameCarrier socket' request' gate' ledger' transport' route'
                            provenance' nameRow' bundle pkg ∧
                          hsame ledger' (append request' gate') ∧ Cont gate' ledger' route' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameSocket sameRequest sameGate sameLedger sameTransport sameRoute
    sameProvenance sameNameRow provenancePkg'
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, _provenancePkg⟩ := carrier
  cases sameSocket
  cases sameRequest
  cases sameGate
  cases sameLedger
  cases sameTransport
  cases sameRoute
  cases sameProvenance
  cases sameNameRow
  constructor
  · exact
      ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
        provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
        gateLedgerNameRow, ledgerSameRequestGate, provenancePkg'⟩
  · constructor
    · exact ledgerSameRequestGate
    · exact gateLedgerRoute

theorem ApophaticNameCarrier_root_bridge_tuple_source [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow downstreamRead →
        PkgSig bundle downstreamRead pkg →
          UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
            UnaryHistory ledger ∧ UnaryHistory transport ∧ UnaryHistory route ∧
              UnaryHistory provenance ∧ UnaryHistory nameRow ∧ UnaryHistory downstreamRead ∧
                Cont socket request gate ∧ Cont request gate route ∧ Cont gate ledger route ∧
                  Cont gate ledger nameRow ∧ Cont ledger nameRow downstreamRead ∧
                    hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier ledgerNameDownstream downstreamPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
    gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameDownstream
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, downstreamUnary, socketRequestGate, requestGateRoute,
      gateLedgerRoute, gateLedgerNameRow, ledgerNameDownstream, ledgerSameRequestGate,
      provenancePkg, downstreamPkg⟩

theorem ApophaticNameCarrier_root_citation_safety [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow citationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont route provenance citationRead →
        PkgSig bundle citationRead pkg →
          UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
            UnaryHistory ledger ∧ UnaryHistory citationRead ∧ Cont socket request gate ∧
              Cont gate ledger route ∧ Cont route provenance citationRead ∧
                hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle citationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier routeProvenanceCitation citationPkg
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, routeUnary,
    provenanceUnary, _nameRowUnary, socketRequestGate, _requestGateRoute, gateLedgerRoute,
    _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have citationUnary : UnaryHistory citationRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceCitation
  exact
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, citationUnary, socketRequestGate,
      gateLedgerRoute, routeProvenanceCitation, ledgerSameRequestGate, provenancePkg,
      citationPkg⟩

end BEDC.Derived.ApophaticNameUp
