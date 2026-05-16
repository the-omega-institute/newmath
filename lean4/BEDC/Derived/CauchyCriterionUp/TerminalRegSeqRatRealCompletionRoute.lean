import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_terminal_regseqrat_real_completion_route
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      cauchyModulus uniformCriterion terminalRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      UnaryHistory cauchyModulus ->
        Cont modulus cauchyModulus uniformCriterion ->
          Cont uniformCriterion realSeal terminalRead ->
            Cont terminalRead endpoint completionRead ->
              PkgSig bundle completionRead pkg ->
                UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
                  UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory cauchyModulus ∧
                    UnaryHistory uniformCriterion ∧ UnaryHistory terminalRead ∧
                      UnaryHistory completionRead ∧ Cont window modulus tolerance ∧
                        Cont tolerance ledger regseq ∧
                          Cont modulus cauchyModulus uniformCriterion ∧
                            Cont uniformCriterion realSeal terminalRead ∧
                              Cont terminalRead endpoint completionRead ∧
                                PkgSig bundle endpoint pkg ∧
                                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier cauchyModulusUnary modulusCauchyUniform uniformRealTerminal
    terminalEndpointCompletion completionPkg
  obtain ⟨windowUnary, modulusUnary, toleranceUnary, _ledgerUnary, regseqUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    windowModulusTolerance, toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have uniformCriterionUnary : UnaryHistory uniformCriterion :=
    unary_cont_closed modulusUnary cauchyModulusUnary modulusCauchyUniform
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed uniformCriterionUnary realSealUnary uniformRealTerminal
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed terminalReadUnary endpointUnary terminalEndpointCompletion
  exact
    ⟨windowUnary, modulusUnary, toleranceUnary, regseqUnary, realSealUnary,
      cauchyModulusUnary, uniformCriterionUnary, terminalReadUnary, completionReadUnary,
      windowModulusTolerance, toleranceLedgerRegseq, modulusCauchyUniform,
      uniformRealTerminal, terminalEndpointCompletion, endpointPkg, completionPkg⟩

end BEDC.Derived.CauchyCriterionUp
