import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_mature_downstream_examples [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      sealRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg →
      Cont ledger realSeal sealRead →
        Cont sealRead provenance completionRead →
          PkgSig bundle sealRead pkg →
            PkgSig bundle completionRead pkg →
              UnaryHistory modulus ∧ UnaryHistory tolerance ∧ UnaryHistory ledger ∧
                UnaryHistory realSeal ∧ UnaryHistory sealRead ∧
                  UnaryHistory completionRead ∧ Cont window modulus tolerance ∧
                    Cont tolerance ledger regseq ∧ Cont ledger realSeal sealRead ∧
                      Cont sealRead provenance completionRead ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle sealRead pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier ledgerRealSealRead sealReadProvenanceCompletionRead sealReadPkg
    completionReadPkg
  obtain ⟨_windowUnary, modulusUnary, toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, provenanceUnary, _localCertUnary,
    _endpointUnary, windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed sealReadUnary provenanceUnary sealReadProvenanceCompletionRead
  exact
    ⟨modulusUnary, toleranceUnary, ledgerUnary, realSealUnary, sealReadUnary,
      completionReadUnary, windowModulusTolerance, toleranceLedgerRegseq,
      ledgerRealSealRead, sealReadProvenanceCompletionRead, endpointPkg, sealReadPkg,
      completionReadPkg⟩

end BEDC.Derived.CauchyCriterionUp
