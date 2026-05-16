import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_diagonal_selector_terminality [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      selectorRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont window ledger selectorRead ->
        Cont selectorRead realSeal terminalRead ->
          PkgSig bundle terminalRead pkg ->
            UnaryHistory window ∧ UnaryHistory modulus ∧ UnaryHistory tolerance ∧
              UnaryHistory ledger ∧ UnaryHistory selectorRead ∧ UnaryHistory terminalRead ∧
                Cont window modulus tolerance ∧ Cont tolerance ledger regseq ∧
                  Cont window ledger selectorRead ∧ Cont selectorRead realSeal terminalRead ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier windowLedgerSelector selectorRealTerminal terminalPkg
  obtain ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    _endpointUnary, windowModulusTolerance, toleranceLedgerRegseq, _regseqRealTransport,
    _transportLocalRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed windowUnary ledgerUnary windowLedgerSelector
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed selectorUnary realSealUnary selectorRealTerminal
  exact
    ⟨windowUnary, modulusUnary, toleranceUnary, ledgerUnary, selectorUnary, terminalUnary,
      windowModulusTolerance, toleranceLedgerRegseq, windowLedgerSelector,
      selectorRealTerminal, endpointPkg, terminalPkg⟩

end BEDC.Derived.CauchyCriterionUp
