import BEDC.Derived.StableNegationBoundaryUp

namespace BEDC.Derived.StableNegationBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StableNegationBoundaryCarrier_certificate_truth_non_escape [AskSetup] [PackageSetup]
    {proposition refutation decision classifier ledger transport route provenance cert
      certificateRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StableNegationBoundaryCarrier proposition refutation decision classifier ledger transport route
        provenance cert bundle pkg ->
      Cont ledger provenance certificateRead ->
        PkgSig bundle certificateRead pkg ->
          UnaryHistory certificateRead /\ Cont ledger provenance certificateRead /\
            PkgSig bundle cert pkg /\ PkgSig bundle certificateRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier ledgerProvenanceCertificate certificatePkg
  obtain ⟨_propositionUnary, _refutationUnary, _decisionUnary, _classifierUnary, ledgerUnary,
    _transportUnary, _routeUnary, provenanceUnary, _certUnary, _propositionRefutationClassifier,
    _decisionClassifierLedger, _ledgerRouteProvenance, certSig⟩ := carrier
  have certificateUnary : UnaryHistory certificateRead :=
    unary_cont_closed ledgerUnary provenanceUnary ledgerProvenanceCertificate
  exact ⟨certificateUnary, ledgerProvenanceCertificate, certSig, certificatePkg⟩

end BEDC.Derived.StableNegationBoundaryUp
