import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_visible_packet_terminal_closure [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      scopedRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont endpoint localCert scopedRead ->
        Cont scopedRead provenance terminalRead ->
          PkgSig bundle scopedRead pkg ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
                UnaryHistory ledger ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
                  UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
                    UnaryHistory localCert ∧ UnaryHistory endpoint ∧
                      UnaryHistory scopedRead ∧ UnaryHistory terminalRead ∧
                        PkgSig bundle endpoint pkg ∧ PkgSig bundle scopedRead pkg ∧
                          PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier endpointLocalCertScopedRead scopedReadProvenanceTerminalRead scopedReadPkg
    terminalReadPkg
  obtain ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
    transportUnary, routeUnary, provenanceUnary, localCertUnary, endpointUnary,
    _windowModulusTolerance, _toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed endpointUnary localCertUnary endpointLocalCertScopedRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed scopedReadUnary provenanceUnary scopedReadProvenanceTerminalRead
  exact
    ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
      transportUnary, routeUnary, provenanceUnary, localCertUnary, endpointUnary,
      scopedReadUnary, terminalReadUnary, endpointPkg, scopedReadPkg, terminalReadPkg⟩

theorem CauchyCriterionClassifier_endpoint_transport_closure [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      window' modulus' tolerance' ledger' regseq' realSeal' transport' route' provenance'
      localCert' endpoint' scopedRead scopedRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionClassifier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint window' modulus' tolerance' ledger' regseq' realSeal'
        transport' route' provenance' localCert' endpoint' bundle pkg ->
      Cont endpoint localCert scopedRead ->
        Cont endpoint' localCert' scopedRead' ->
          hsame scopedRead scopedRead' ∧ UnaryHistory scopedRead ∧ UnaryHistory scopedRead' := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro classifier endpointLocalCertScopedRead endpointLocalCertScopedRead'
  obtain ⟨carrier, carrier', _sameWindow, _sameModulus, _sameTolerance, _sameLedger,
    _sameRegseq, _sameRealSeal, _sameTransport, _sameRoute, _sameProvenance,
    sameLocalCert, sameEndpoint⟩ := classifier
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
    _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    _endpointPkg⟩ := carrier
  obtain ⟨_windowUnary', _modulusUnary', _toleranceUnary', _ledgerUnary', _regseqUnary',
    _realSealUnary', _transportUnary', _routeUnary', _provenanceUnary', localCertUnary',
    endpointUnary', _windowModulusTolerance', _toleranceLedgerRegseq',
    _regseqRealSealTransport', _transportLocalCertRoute', _routeProvenanceEndpoint',
    _endpointPkg'⟩ := carrier'
  have sameScopedRead : hsame scopedRead scopedRead' :=
    cont_respects_hsame sameEndpoint sameLocalCert endpointLocalCertScopedRead
      endpointLocalCertScopedRead'
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed endpointUnary localCertUnary endpointLocalCertScopedRead
  have scopedReadUnary' : UnaryHistory scopedRead' :=
    unary_cont_closed endpointUnary' localCertUnary' endpointLocalCertScopedRead'
  exact ⟨sameScopedRead, scopedReadUnary, scopedReadUnary'⟩

end BEDC.Derived.CauchyCriterionUp
