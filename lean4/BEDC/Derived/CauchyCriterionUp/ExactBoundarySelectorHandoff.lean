import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_exact_boundary_selector_handoff [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      selectorRead exactBoundaryRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont ledger realSeal selectorRead ->
        Cont selectorRead endpoint exactBoundaryRead ->
          Cont exactBoundaryRead realSeal terminalRead ->
            PkgSig bundle selectorRead pkg ->
              PkgSig bundle exactBoundaryRead pkg ->
                PkgSig bundle terminalRead pkg ->
                  UnaryHistory selectorRead ∧ UnaryHistory exactBoundaryRead ∧
                    UnaryHistory terminalRead ∧ Cont ledger realSeal selectorRead ∧
                      Cont selectorRead endpoint exactBoundaryRead ∧
                        Cont exactBoundaryRead realSeal terminalRead ∧
                          PkgSig bundle endpoint pkg ∧ PkgSig bundle selectorRead pkg ∧
                            PkgSig bundle exactBoundaryRead pkg ∧
                              PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier ledgerRealSelector selectorEndpointExact exactRealTerminal selectorPkg
    exactPkg terminalPkg
  rcases carrier with
    ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
      realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
      endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
      _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
      endpointPkg⟩
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSelector
  have exactUnary : UnaryHistory exactBoundaryRead :=
    unary_cont_closed selectorUnary endpointUnary selectorEndpointExact
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed exactUnary realSealUnary exactRealTerminal
  exact
    ⟨selectorUnary, exactUnary, terminalUnary, ledgerRealSelector, selectorEndpointExact,
      exactRealTerminal, endpointPkg, selectorPkg, exactPkg, terminalPkg⟩

end BEDC.Derived.CauchyCriterionUp
