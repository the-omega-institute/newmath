import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_real_tail_agreement_seal_route_correspondence
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert
      endpoint tailAgreement completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont ledger realSeal tailAgreement ->
        Cont tailAgreement endpoint completionRead ->
          PkgSig bundle completionRead pkg ->
            UnaryHistory tailAgreement ∧ UnaryHistory completionRead ∧
              Cont window modulus tolerance ∧ Cont tolerance ledger regseq ∧
                Cont ledger realSeal tailAgreement ∧
                  Cont tailAgreement endpoint completionRead ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier ledgerRealTail tailEndpointCompletion completionPkg
  rcases carrier with
    ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
      realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
      endpointUnary, windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
      _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩
  have tailAgreementUnary : UnaryHistory tailAgreement :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealTail
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed tailAgreementUnary endpointUnary tailEndpointCompletion
  exact
    ⟨tailAgreementUnary, completionReadUnary, windowModulusTolerance, toleranceLedgerRegseq,
      ledgerRealTail, tailEndpointCompletion, endpointPkg, completionPkg⟩

end BEDC.Derived.CauchyCriterionUp
