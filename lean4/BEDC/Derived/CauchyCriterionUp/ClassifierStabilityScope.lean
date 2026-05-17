import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_classified_tail_budget_transport [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      window' modulus' tolerance' ledger' regseq' realSeal' transport' route' provenance'
      localCert' endpoint' tailConsumer tailConsumer' handoff handoff' sealRead sealRead' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      hsame window window' ->
        hsame modulus modulus' ->
          hsame ledger ledger' ->
            hsame realSeal realSeal' ->
              hsame provenance provenance' ->
                hsame localCert localCert' ->
                  Cont window' modulus' tolerance' ->
                    Cont tolerance' ledger' regseq' ->
                      Cont regseq' realSeal' transport' ->
                        Cont transport' localCert' route' ->
                          Cont route' provenance' endpoint' ->
                            PkgSig bundle endpoint' pkg ->
                              Cont ledger provenance tailConsumer ->
                                Cont ledger' provenance' tailConsumer' ->
                                  Cont regseq realSeal handoff ->
                                    Cont regseq' realSeal' handoff' ->
                                      Cont ledger realSeal sealRead ->
                                        Cont ledger' realSeal' sealRead' ->
                                          hsame tailConsumer tailConsumer' ∧
                                            hsame handoff handoff' ∧
                                              hsame sealRead sealRead' ∧
                                                UnaryHistory tailConsumer' ∧
                                                  UnaryHistory handoff' ∧
                                                    UnaryHistory sealRead' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory ProbeBundle Pkg
  intro carrier sameWindow sameModulus sameLedger sameRealSeal sameProvenance sameLocalCert
    toleranceRow' regseqRow' transportRow' routeRow' endpointRow' endpointPkg'
    ledgerProvenanceTailConsumer ledgerProvenanceTailConsumer' regseqRealSealHandoff
    regseqRealSealHandoff' ledgerRealSealSealRead ledgerRealSealSealRead'
  have transported :=
    CauchyCriterionCarrier_modulus_threshold_stability
      (window := window) (modulus := modulus) (tolerance := tolerance)
      (ledger := ledger) (regseq := regseq) (realSeal := realSeal)
      (transport := transport) (route := route) (provenance := provenance)
      (localCert := localCert) (endpoint := endpoint) (window' := window')
      (modulus' := modulus') (tolerance' := tolerance') (ledger' := ledger')
      (regseq' := regseq') (realSeal' := realSeal') (transport' := transport')
      (route' := route') (provenance' := provenance') (localCert' := localCert')
      (endpoint' := endpoint') (bundle := bundle) (pkg := pkg) carrier sameWindow
      sameModulus sameLedger sameRealSeal sameProvenance sameLocalCert toleranceRow'
      regseqRow' transportRow' routeRow' endpointRow' endpointPkg'
  obtain ⟨targetCarrier, _sameTolerance, sameRegseq, _sameTransport, _sameRoute,
    _sameEndpoint⟩ := transported
  obtain ⟨_windowUnary', _modulusUnary', _toleranceUnary', ledgerUnary', regseqUnary',
    realSealUnary', _transportUnary', _routeUnary', provenanceUnary', _localCertUnary',
    _endpointUnary', _toleranceRow'', _regseqRow'', _transportRow'', _routeRow'',
    _endpointRow'', _endpointPkg''⟩ := targetCarrier
  have sameTailConsumer : hsame tailConsumer tailConsumer' :=
    cont_respects_hsame sameLedger sameProvenance ledgerProvenanceTailConsumer
      ledgerProvenanceTailConsumer'
  have sameHandoff : hsame handoff handoff' :=
    cont_respects_hsame sameRegseq sameRealSeal regseqRealSealHandoff
      regseqRealSealHandoff'
  have sameSealRead : hsame sealRead sealRead' :=
    cont_respects_hsame sameLedger sameRealSeal ledgerRealSealSealRead
      ledgerRealSealSealRead'
  have tailConsumerUnary' : UnaryHistory tailConsumer' :=
    unary_cont_closed ledgerUnary' provenanceUnary' ledgerProvenanceTailConsumer'
  have handoffUnary' : UnaryHistory handoff' :=
    unary_cont_closed regseqUnary' realSealUnary' regseqRealSealHandoff'
  have sealReadUnary' : UnaryHistory sealRead' :=
    unary_cont_closed ledgerUnary' realSealUnary' ledgerRealSealSealRead'
  exact
    ⟨sameTailConsumer, sameHandoff, sameSealRead, tailConsumerUnary', handoffUnary',
      sealReadUnary'⟩

end BEDC.Derived.CauchyCriterionUp
