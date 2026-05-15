import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_streamname_real_budget_selector_boundary
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      selectorOutput : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont endpoint realSeal selectorOutput ->
        PkgSig bundle selectorOutput pkg ->
          UnaryHistory window ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
            UnaryHistory selectorOutput ∧ Cont endpoint realSeal selectorOutput ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle selectorOutput pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier endpointRealSealSelector selectorOutputPkg
  rcases carrier with
    ⟨windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, regseqUnary,
      realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
      endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
      _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
      endpointPkg⟩
  have selectorOutputUnary : UnaryHistory selectorOutput :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSealSelector
  exact
    ⟨windowUnary, regseqUnary, realSealUnary, selectorOutputUnary,
      endpointRealSealSelector, endpointPkg, selectorOutputPkg⟩

end BEDC.Derived.CauchyCriterionUp
