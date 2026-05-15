import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_uniform_family_quotient_refusal_factorization
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert
      endpoint quotientRequest refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg →
      UnaryHistory quotientRequest →
        Cont endpoint quotientRequest refusalRead →
          PkgSig bundle refusalRead pkg →
            UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
              UnaryHistory ledger ∧ UnaryHistory regseq ∧ UnaryHistory realSeal ∧
                UnaryHistory endpoint ∧ UnaryHistory quotientRequest ∧
                  UnaryHistory refusalRead ∧ Cont window modulus tolerance ∧
                    Cont tolerance ledger regseq ∧ Cont route provenance endpoint ∧
                      Cont endpoint quotientRequest refusalRead ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier quotientRequestUnary endpointQuotientRefusal refusalReadPkg
  obtain ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed endpointUnary quotientRequestUnary endpointQuotientRefusal
  exact
    ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, regseqUnary, realSealUnary,
      endpointUnary, quotientRequestUnary, refusalReadUnary, windowModulusTolerance,
      toleranceLedgerRegseq, routeProvenanceEndpoint, endpointQuotientRefusal, endpointPkg,
      refusalReadPkg⟩

end BEDC.Derived.CauchyCriterionUp
