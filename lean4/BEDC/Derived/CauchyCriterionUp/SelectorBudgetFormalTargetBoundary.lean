import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_selector_budget_formal_target_boundary
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      selectorRead formalTargetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont endpoint realSeal selectorRead ->
        Cont selectorRead localCert formalTargetRead ->
          PkgSig bundle formalTargetRead pkg ->
            UnaryHistory endpoint ∧ UnaryHistory selectorRead ∧ UnaryHistory formalTargetRead ∧
              Cont endpoint realSeal selectorRead ∧ Cont selectorRead localCert formalTargetRead ∧
                PkgSig bundle endpoint pkg ∧ PkgSig bundle formalTargetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier endpointRealSealSelector selectorLocalCertFormal formalTargetPkg
  rcases carrier with
    ⟨_windowUnary, _modulusUnary, _toleranceUnary, _ledgerUnary, _regseqUnary,
      realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, localCertUnary,
      endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
      _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
      endpointPkg⟩
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSealSelector
  have formalTargetUnary : UnaryHistory formalTargetRead :=
    unary_cont_closed selectorUnary localCertUnary selectorLocalCertFormal
  exact
    ⟨endpointUnary, selectorUnary, formalTargetUnary, endpointRealSealSelector,
      selectorLocalCertFormal, endpointPkg, formalTargetPkg⟩

end BEDC.Derived.CauchyCriterionUp
