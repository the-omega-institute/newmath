import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_real_tail_agreement_route_correspondence
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert
      endpoint agreementRead agreementSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont regseq realSeal agreementRead ->
        Cont agreementRead provenance agreementSeal ->
          PkgSig bundle agreementSeal pkg ->
            UnaryHistory agreementRead ∧ UnaryHistory agreementSeal ∧
              hsame agreementRead transport ∧ Cont regseq realSeal agreementRead ∧
                Cont agreementRead provenance agreementSeal ∧
                  PkgSig bundle agreementSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro carrier agreementReadRow agreementSealRow agreementSealPkg
  rcases carrier with
    ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, regseqUnary,
      realSealUnary, _transportUnary, _routeUnary, provenanceUnary, _localCertUnary,
      _endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
      carrierTransportRow, _transportLocalCertRoute, _routeProvenanceEndpoint, _endpointPkg⟩
  have agreementReadUnary : UnaryHistory agreementRead :=
    unary_cont_closed regseqUnary realSealUnary agreementReadRow
  have agreementSealUnary : UnaryHistory agreementSeal :=
    unary_cont_closed agreementReadUnary provenanceUnary agreementSealRow
  have sameAgreementReadTransport : hsame agreementRead transport :=
    hsame_symm
      (cont_respects_hsame (hsame_refl regseq) (hsame_refl realSeal) carrierTransportRow
        agreementReadRow)
  exact
    ⟨agreementReadUnary, agreementSealUnary, sameAgreementReadTransport, agreementReadRow,
      agreementSealRow, agreementSealPkg⟩

end BEDC.Derived.CauchyCriterionUp
