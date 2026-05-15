import BEDC.Derived.ApophaticNameUp.RootDownstreamSocketNonescape
import BEDC.Derived.ApophaticNameUp.RootRefusalBoundaryExhaustion
import BEDC.Derived.ApophaticNameUp.SupplyShapeNoninternalization

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_downstream_socket_ledger_factorization [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead downstreamRead
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow socketRead →
        Cont socketRead provenance downstreamRead →
          Cont ledger nameRow rootRead →
            PkgSig bundle downstreamRead pkg →
              PkgSig bundle rootRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      ApophaticNameCarrier socket request gate ledger transport route
                        provenance nameRow bundle pkg ∧ hsame row socket)
                    (fun row : BHist => hsame row socket ∧ UnaryHistory row)
                    (fun _row : BHist =>
                      Cont socket request gate ∧ Cont ledger nameRow socketRead ∧
                        PkgSig bundle provenance pkg)
                    hsame ∧
                  SemanticNameCert
                      (fun row : BHist =>
                        ApophaticNameCarrier socket request gate ledger transport route
                          provenance nameRow bundle pkg ∧ hsame row ledger)
                      (fun row : BHist => hsame row (append request gate) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
                          hsame row (append request gate) ∧ Cont ledger nameRow rootRead)
                      hsame ∧
                    UnaryHistory socketRead ∧
                    UnaryHistory downstreamRead ∧
                    UnaryHistory rootRead ∧
                    Cont ledger nameRow socketRead ∧
                    Cont socketRead provenance downstreamRead ∧
                    hsame ledger (append request gate) ∧
                    PkgSig bundle downstreamRead pkg ∧
                    PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameSocket socketReadProvenance ledgerNameRoot downstreamPkg rootPkg
  have downstream :=
    ApophaticNameCarrier_root_downstream_socket_nonescape
      (socket := socket) (request := request) (gate := gate) (ledger := ledger)
      (transport := transport) (route := route) (provenance := provenance)
      (nameRow := nameRow) (socketRead := socketRead) (downstreamRead := downstreamRead)
      (bundle := bundle) (pkg := pkg)
      carrier ledgerNameSocket socketReadProvenance downstreamPkg
  have root :=
    ApophaticNameCarrier_root_refusal_boundary_exhaustion
      (socket := socket) (request := request) (gate := gate) (ledger := ledger)
      (transport := transport) (route := route) (provenance := provenance)
      (nameRow := nameRow) (rootRead := rootRead) (bundle := bundle) (pkg := pkg)
      carrier ledgerNameRoot rootPkg
  obtain ⟨socketCert, socketReadUnary, downstreamUnary, ledgerNameSocketRow,
    socketReadProvenanceRow, downstreamPkgRow⟩ := downstream
  obtain ⟨ledgerCert, _socketUnary, _requestUnary, _gateUnary, _ledgerUnary, rootUnary,
    _socketRequestGate, _ledgerNameRootRow, ledgerSameRequestGate, rootPkgRow⟩ := root
  exact
    ⟨socketCert, ledgerCert, socketReadUnary, downstreamUnary, rootUnary,
      ledgerNameSocketRow, socketReadProvenanceRow, ledgerSameRequestGate, downstreamPkgRow,
      rootPkgRow⟩

theorem ApophaticNameCarrier_root_refusal_terminal_nonpromotion [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socketRead downstreamRead
      supplyRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont ledger nameRow socketRead →
        PkgSig bundle socketRead pkg →
          Cont socketRead provenance downstreamRead →
            PkgSig bundle downstreamRead pkg →
              Cont request gate supplyRead →
                PkgSig bundle supplyRead pkg →
                  Cont downstreamRead ledger terminalRead →
                    PkgSig bundle terminalRead pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            ApophaticNameCarrier socket request gate ledger transport route
                              provenance nameRow bundle pkg ∧ hsame row request)
                          (fun row : BHist => hsame row request ∧ UnaryHistory row)
                          (fun row : BHist =>
                            PkgSig bundle provenance pkg ∧ PkgSig bundle supplyRead pkg ∧
                              hsame row request ∧ Cont request gate supplyRead)
                          hsame ∧
                        SemanticNameCert
                            (fun row : BHist =>
                              ApophaticNameCarrier socket request gate ledger transport route
                                provenance nameRow bundle pkg ∧ hsame row ledger)
                            (fun row : BHist =>
                              hsame row (append request gate) ∧ UnaryHistory row)
                            (fun row : BHist =>
                              PkgSig bundle provenance pkg ∧ PkgSig bundle socketRead pkg ∧
                                hsame row (append request gate) ∧
                                  Cont ledger nameRow socketRead)
                            hsame ∧
                          UnaryHistory supplyRead ∧
                          UnaryHistory downstreamRead ∧
                          UnaryHistory terminalRead ∧
                          Cont request gate supplyRead ∧
                          Cont downstreamRead ledger terminalRead ∧
                          PkgSig bundle supplyRead pkg ∧
                          PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier ledgerNameSocket socketReadPkg socketReadProvenance downstreamPkg
    requestGateSupply supplyPkg downstreamLedgerTerminal terminalPkg
  have supply :=
    ApophaticNameCarrier_supply_shape_noninternalization
      (socket := socket) (request := request) (gate := gate) (ledger := ledger)
      (transport := transport) (route := route) (provenance := provenance)
      (nameRow := nameRow) (supplyRead := supplyRead) (bundle := bundle) (pkg := pkg)
      carrier requestGateSupply supplyPkg
  have root :=
    ApophaticNameCarrier_root_refusal_boundary_exhaustion
      (socket := socket) (request := request) (gate := gate) (ledger := ledger)
      (transport := transport) (route := route) (provenance := provenance)
      (nameRow := nameRow) (rootRead := socketRead) (bundle := bundle) (pkg := pkg)
      carrier ledgerNameSocket socketReadPkg
  obtain ⟨supplyCert, _requestUnary, supplyUnary, requestGateSupplyRow, supplyPkgRow⟩ :=
    supply
  obtain ⟨ledgerCert, _socketUnary, _requestUnaryFromRoot, _gateUnary, ledgerUnary,
    _socketReadUnary, _socketRequestGate, ledgerNameSocketRow, _ledgerSameRequestGate,
    _socketReadPkgRow⟩ := root
  have downstreamUnary : UnaryHistory downstreamRead := by
    obtain ⟨_socketUnary, _requestUnaryCarrier, _gateUnaryCarrier, _ledgerUnaryCarrier,
      _transportUnary, _routeUnary, provenanceUnary, nameRowUnary, _socketRequestGateCarrier,
      _requestGateRoute, _gateLedgerRoute, _gateLedgerNameRow, _ledgerSameRequestGateCarrier,
      _provenancePkg⟩ := carrier
    have socketReadUnary : UnaryHistory socketRead :=
      unary_cont_closed ledgerUnary nameRowUnary ledgerNameSocketRow
    exact unary_cont_closed socketReadUnary provenanceUnary socketReadProvenance
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed downstreamUnary ledgerUnary downstreamLedgerTerminal
  exact
    ⟨supplyCert, ledgerCert, supplyUnary, downstreamUnary, terminalUnary,
      requestGateSupplyRow, downstreamLedgerTerminal, supplyPkgRow, terminalPkg⟩

end BEDC.Derived.ApophaticNameUp
