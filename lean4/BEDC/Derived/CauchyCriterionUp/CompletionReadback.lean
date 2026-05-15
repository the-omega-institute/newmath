import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_completion_facing_readback_normal_form
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert
      endpoint completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont endpoint realSeal completionRead ->
        PkgSig bundle completionRead pkg ->
          UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
            UnaryHistory ledger ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
              UnaryHistory endpoint ∧ UnaryHistory completionRead ∧
                Cont window modulus tolerance ∧ Cont tolerance ledger regseq ∧
                  Cont route provenance endpoint ∧ Cont endpoint realSeal completionRead ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier endpointRealSealCompletion completionPkg
  obtain ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSealCompletion
  exact
    ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
      endpointUnary, completionUnary, windowModulusTolerance, toleranceLedgerRegseq,
      routeProvenanceEndpoint, endpointRealSealCompletion, endpointPkg, completionPkg⟩

end BEDC.Derived.CauchyCriterionUp
