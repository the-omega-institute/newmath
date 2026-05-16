import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_tail_budget_real_completion_boundary [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert
      endpoint completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont modulus tolerance ledger ->
        Cont ledger regseq completionRead ->
          PkgSig bundle completionRead pkg ->
            UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
              UnaryHistory ledger ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
                UnaryHistory completionRead ∧ Cont window modulus tolerance ∧
                  Cont tolerance ledger regseq ∧ Cont modulus tolerance ledger ∧
                    Cont ledger regseq completionRead ∧ PkgSig bundle endpoint pkg ∧
                      PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier modulusToleranceLedger ledgerRegseqCompletion completionPkg
  obtain ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed ledgerUnary regseqUnary ledgerRegseqCompletion
  exact
    ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
      completionUnary, windowModulusTolerance, toleranceLedgerRegseq, modulusToleranceLedger,
      ledgerRegseqCompletion, endpointPkg, completionPkg⟩

end BEDC.Derived.CauchyCriterionUp
