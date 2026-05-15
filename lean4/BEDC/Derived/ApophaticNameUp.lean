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

theorem ApophaticNameCarrier_root_socket_gate_factorization [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow rootRead →
        PkgSig bundle rootRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row socket ∧
                  ApophaticNameCarrier socket request gate ledger transport route provenance
                    nameRow bundle pkg)
              (fun row : BHist => hsame row socket ∧ UnaryHistory socket)
              (fun _row : BHist =>
                Cont socket request gate ∧ Cont gate ledger nameRow ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory socket ∧
            UnaryHistory request ∧
            UnaryHistory gate ∧
            UnaryHistory ledger ∧
            UnaryHistory rootRead ∧
            Cont socket request gate ∧
            Cont gate ledger nameRow ∧
            Cont ledger nameRow rootRead ∧
            hsame ledger (append request gate) ∧
            PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameRoot rootPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameRoot
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row socket ∧
              ApophaticNameCarrier socket request gate ledger transport route provenance
                nameRow bundle pkg)
          (fun row : BHist => hsame row socket ∧ UnaryHistory socket)
          (fun _row : BHist =>
            Cont socket request gate ∧ Cont gate ledger nameRow ∧
              PkgSig bundle provenance pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro socket (And.intro (hsame_refl socket) carrierPacket)
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    · intro row source
      exact ⟨source.left, socketUnary⟩
    · intro row _source
      exact ⟨socketRequestGate, gateLedgerNameRow, provenancePkg⟩
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, rootUnary, socketRequestGate,
      gateLedgerNameRow, ledgerNameRoot, ledgerSameRequestGate, rootPkg⟩

theorem ApophaticNameCarrier_refusal_ledger_exactness [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow downstreamRead →
        PkgSig bundle downstreamRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance
                  nameRow bundle pkg ∧ hsame row ledger)
              (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ hsame row ledger ∧ Cont gate ledger nameRow)
              hsame ∧
            UnaryHistory ledger ∧ Cont ledger nameRow downstreamRead ∧
              PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameDownstream downstreamPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance
              nameRow bundle pkg ∧ hsame row ledger)
          (fun row : BHist => hsame row ledger ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ hsame row ledger ∧ Cont gate ledger nameRow)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger ⟨carrierPacket, hsame_refl ledger⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      exact ⟨source.right, unary_transport ledgerUnary (hsame_symm source.right)⟩
    · intro row source
      exact ⟨provenancePkg, source.right, gateLedgerNameRow⟩
  exact ⟨cert, ledgerUnary, ledgerNameDownstream, downstreamPkg⟩

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

theorem ApophaticNameCarrier_root_bridge_tuple_classifier [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow classifierRead →
        PkgSig bundle classifierRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                  bundle pkg ∧ hsame row ledger)
              (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ hsame row (append request gate) ∧
                  Cont gate ledger nameRow)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
            UnaryHistory ledger ∧ UnaryHistory classifierRead ∧
            Cont socket request gate ∧ Cont gate ledger nameRow ∧
            Cont ledger nameRow classifierRead ∧ hsame ledger (append request gate) ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameClassifier classifierPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameClassifier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg ∧ hsame row ledger)
          (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ hsame row (append request gate) ∧
              Cont gate ledger nameRow)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro ledger ⟨carrierPacket, hsame_refl ledger⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameLedger : hsame row ledger := source.right
      exact
        ⟨hsame_trans rowSameLedger ledgerSameRequestGate,
          unary_transport ledgerUnary (hsame_symm rowSameLedger)⟩
    · intro row source
      have rowSameLedger : hsame row ledger := source.right
      exact
        ⟨provenancePkg, hsame_trans rowSameLedger ledgerSameRequestGate,
          gateLedgerNameRow⟩
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, classifierUnary,
      socketRequestGate, gateLedgerNameRow, ledgerNameClassifier, ledgerSameRequestGate,
      provenancePkg, classifierPkg⟩

theorem ApophaticNameCarrier_root_stdbridge_premise_surface [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socket' request' gate'
      ledger' transport' route' provenance' nameRow' bridgeRead : BHist}
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
                        Cont ledger' nameRow' bridgeRead →
                          PkgSig bundle bridgeRead pkg →
                            ApophaticNameCarrier socket' request' gate' ledger' transport'
                                route' provenance' nameRow' bundle pkg ∧
                              SemanticNameCert
                                  (fun row : BHist =>
                                    ApophaticNameCarrier socket' request' gate' ledger'
                                      transport' route' provenance' nameRow' bundle pkg ∧
                                      hsame row nameRow')
                                  (fun row : BHist => hsame row nameRow' ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    PkgSig bundle provenance' pkg ∧ hsame row nameRow' ∧
                                      Cont ledger' nameRow' bridgeRead)
                                  hsame ∧
                                UnaryHistory bridgeRead ∧
                                hsame ledger' (append request' gate') ∧
                                Cont gate' ledger' nameRow' ∧
                                PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier sameSocket sameRequest sameGate sameLedger sameTransport sameRoute
    sameProvenance sameNameRow provenancePkg' ledgerNameBridge bridgePkg
  have transported :=
    ApophaticNameCarrier_refusal_transport_totality
      (socket := socket) (request := request) (gate := gate) (ledger := ledger)
      (transport := transport) (route := route) (provenance := provenance)
      (nameRow := nameRow) (socket' := socket') (request' := request') (gate' := gate')
      (ledger' := ledger') (transport' := transport') (route' := route')
      (provenance' := provenance') (nameRow' := nameRow') (bundle := bundle) (pkg := pkg)
      carrier sameSocket sameRequest sameGate sameLedger sameTransport sameRoute sameProvenance
      sameNameRow provenancePkg'
  have transported_carrier :
      ApophaticNameCarrier socket' request' gate' ledger' transport' route' provenance'
        nameRow' bundle pkg :=
    transported.left
  have ledger_same_request_gate_prime : hsame ledger' (append request' gate') :=
    transported.right.left
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary', _transportUnary,
    _routeUnary, _provenanceUnary, nameRowUnary', _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, gateLedgerNameRowPrime, _ledgerSameRequestGate, _provenancePkg⟩ :=
    transported_carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed ledgerUnary' nameRowUnary' ledgerNameBridge
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket' request' gate' ledger' transport' route' provenance'
              nameRow' bundle pkg ∧ hsame row nameRow')
          (fun row : BHist => hsame row nameRow' ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance' pkg ∧ hsame row nameRow' ∧
              Cont ledger' nameRow' bridgeRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro nameRow' ⟨transported.left, hsame_refl nameRow'⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameName : hsame row nameRow' := source.right
      exact
        ⟨rowSameName, unary_transport nameRowUnary' (hsame_symm rowSameName)⟩
    · intro row source
      exact ⟨provenancePkg', source.right, ledgerNameBridge⟩
  exact
    ⟨transported.left, cert, bridgeUnary, ledger_same_request_gate_prime, gateLedgerNameRowPrime,
      bridgePkg⟩

theorem ApophaticNameCarrier_root_unblock_public_citation_surface [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow bundle pkg →
      Cont route provenance publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
                  bundle pkg ∧ hsame row provenance)
              (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ hsame row provenance ∧
                  Cont route provenance publicRead)
              hsame ∧
            UnaryHistory publicRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeProvenancePublic publicPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, _ledgerUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGate, provenancePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenancePublic
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg ∧ hsame row provenance)
          (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ hsame row provenance ∧
              Cont route provenance publicRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro provenance ⟨carrierPacket, hsame_refl provenance⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSameProvenance : hsame row provenance := source.right
      exact
        ⟨rowSameProvenance,
          unary_transport provenanceUnary (hsame_symm rowSameProvenance)⟩
    · intro row source
      exact ⟨provenancePkg, source.right, routeProvenancePublic⟩
  exact ⟨cert, publicUnary, provenancePkg, publicPkg⟩

theorem ApophaticNameCarrier_root_bridge_counter_surface [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow bridgeRead counterRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow bridgeRead →
        PkgSig bundle bridgeRead pkg →
          Cont bridgeRead provenance counterRead →
            PkgSig bundle counterRead pkg →
              UnaryHistory bridgeRead ∧ UnaryHistory counterRead ∧
                Cont ledger nameRow bridgeRead ∧ Cont bridgeRead provenance counterRead ∧
                  hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle bridgeRead pkg ∧ PkgSig bundle counterRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier ledgerNameBridge bridgePkg bridgeProvenanceCounter counterPkg
  obtain ⟨_socketUnary, _requestUnary, _gateUnary, ledgerUnary, _transportUnary,
    _routeUnary, provenanceUnary, nameRowUnary, _socketRequestGate, _requestGateRoute,
    _gateLedgerRoute, _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed ledgerUnary nameRowUnary ledgerNameBridge
  have counterUnary : UnaryHistory counterRead :=
    unary_cont_closed bridgeUnary provenanceUnary bridgeProvenanceCounter
  exact
    ⟨bridgeUnary, counterUnary, ledgerNameBridge, bridgeProvenanceCounter,
      ledgerSameRequestGate, provenancePkg, bridgePkg, counterPkg⟩

end BEDC.Derived.ApophaticNameUp
