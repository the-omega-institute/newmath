import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_refusal_provenance_transport [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socket' request' gate' ledger'
      transport' route' provenance' nameRow' citationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      hsame socket socket' ->
        hsame request request' ->
          hsame gate gate' ->
            hsame ledger ledger' ->
              hsame transport transport' ->
                hsame route route' ->
                  hsame provenance provenance' ->
                    hsame nameRow nameRow' ->
                      Cont route' provenance' citationRead ->
                        PkgSig bundle provenance' pkg ->
                          PkgSig bundle citationRead pkg ->
                            ApophaticNameCarrier socket' request' gate' ledger' transport'
                                route' provenance' nameRow' bundle pkg ∧
                              UnaryHistory citationRead ∧
                                Cont route' provenance' citationRead ∧
                                  hsame ledger' (append request' gate') ∧
                                    PkgSig bundle citationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sameSocket sameRequest sameGate sameLedger sameTransport sameRoute
    sameProvenance sameNameRow routeProvenanceCitation provenancePkg' citationPkg
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
  have citationUnary : UnaryHistory citationRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceCitation
  have transportedCarrier :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
      gateLedgerNameRow, ledgerSameRequestGate, provenancePkg'⟩
  exact
    ⟨transportedCarrier, citationUnary, routeProvenanceCitation, ledgerSameRequestGate,
      citationPkg⟩

theorem ApophaticNameRefusalProvenanceTransport [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow socket' request' gate'
      ledger' transport' route' provenance' nameRow' downstreamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg ->
      hsame socket socket' ->
        hsame request request' ->
          hsame gate gate' ->
            hsame ledger ledger' ->
              hsame transport transport' ->
                hsame route route' ->
                  hsame provenance provenance' ->
                    hsame nameRow nameRow' ->
                      Cont ledger' nameRow' downstreamRead ->
                        PkgSig bundle provenance' pkg ->
                          PkgSig bundle downstreamRead pkg ->
                            ApophaticNameCarrier socket' request' gate' ledger'
                                transport' route' provenance' nameRow' bundle pkg ∧
                              UnaryHistory downstreamRead ∧
                                hsame ledger' (append request' gate') ∧
                                  Cont gate' ledger' route' ∧
                                    Cont ledger' nameRow' downstreamRead ∧
                                      PkgSig bundle provenance' pkg ∧
                                        PkgSig bundle downstreamRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont PkgSig UnaryHistory
  intro carrier sameSocket sameRequest sameGate sameLedger sameTransport sameRoute
    sameProvenance sameNameRow downstreamRoute provenancePkg' downstreamPkg
  rcases carrier with
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
      gateLedgerNameRow, ledgerSameRequestGate, _provenancePkg⟩
  cases sameSocket
  cases sameRequest
  cases sameGate
  cases sameLedger
  cases sameTransport
  cases sameRoute
  cases sameProvenance
  cases sameNameRow
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed ledgerUnary nameRowUnary downstreamRoute
  have transportedCarrier :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, transportUnary, routeUnary,
      provenanceUnary, nameRowUnary, socketRequestGate, requestGateRoute, gateLedgerRoute,
      gateLedgerNameRow, ledgerSameRequestGate, provenancePkg'⟩
  exact
    ⟨transportedCarrier, downstreamUnary, ledgerSameRequestGate, gateLedgerRoute,
      downstreamRoute, provenancePkg', downstreamPkg⟩

end BEDC.Derived.ApophaticNameUp
