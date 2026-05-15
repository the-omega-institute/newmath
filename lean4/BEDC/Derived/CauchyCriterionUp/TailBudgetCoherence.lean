import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_tail_budget_coherence_consumption [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      tailConsumer handoff sealRead coherenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont ledger provenance tailConsumer ->
        Cont regseq realSeal handoff ->
          Cont ledger realSeal sealRead ->
            Cont tailConsumer sealRead coherenceRead ->
              PkgSig bundle tailConsumer pkg ->
                PkgSig bundle handoff pkg ->
                  PkgSig bundle sealRead pkg ->
                    PkgSig bundle coherenceRead pkg ->
                      UnaryHistory tailConsumer ∧ UnaryHistory handoff ∧
                        UnaryHistory sealRead ∧ UnaryHistory coherenceRead ∧
                          Cont ledger provenance tailConsumer ∧ Cont regseq realSeal handoff ∧
                            Cont ledger realSeal sealRead ∧
                              Cont tailConsumer sealRead coherenceRead ∧
                                PkgSig bundle endpoint pkg ∧
                                  PkgSig bundle coherenceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier ledgerProvenanceTailConsumer regseqRealSealHandoff ledgerRealSealSealRead
    tailConsumerSealCoherence tailConsumerPkg handoffPkg sealReadPkg coherencePkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, provenanceUnary, _localCertUnary,
    _endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  have tailConsumerUnary : UnaryHistory tailConsumer :=
    unary_cont_closed ledgerUnary provenanceUnary ledgerProvenanceTailConsumer
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealHandoff
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealSealRead
  have coherenceUnary : UnaryHistory coherenceRead :=
    unary_cont_closed tailConsumerUnary sealReadUnary tailConsumerSealCoherence
  exact
    ⟨tailConsumerUnary, handoffUnary, sealReadUnary, coherenceUnary,
      ledgerProvenanceTailConsumer, regseqRealSealHandoff, ledgerRealSealSealRead,
      tailConsumerSealCoherence, endpointPkg, coherencePkg⟩

end BEDC.Derived.CauchyCriterionUp
