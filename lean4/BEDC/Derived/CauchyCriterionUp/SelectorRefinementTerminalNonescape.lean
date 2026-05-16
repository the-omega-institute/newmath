import BEDC.Derived.CauchyCriterionUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_selector_refinement_terminal_nonescape [AskSetup]
    [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      selectorRead sealRead terminalRead hostLimit quotient : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      Cont ledger realSeal selectorRead ->
        Cont selectorRead provenance sealRead ->
          Cont sealRead endpoint terminalRead ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory selectorRead ∧ UnaryHistory sealRead ∧
                UnaryHistory terminalRead ∧ Cont ledger realSeal selectorRead ∧
                  Cont selectorRead provenance sealRead ∧ Cont sealRead endpoint terminalRead ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle terminalRead pkg ∧
                      (Cont terminalRead (BHist.e0 hostLimit) selectorRead -> False) ∧
                        (Cont terminalRead (BHist.e1 quotient) sealRead -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier ledgerRealSelector selectorProvenanceSeal sealEndpointTerminal terminalPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, provenanceUnary, _localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSelector
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed selectorUnary provenanceUnary selectorProvenanceSeal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed sealReadUnary endpointUnary sealEndpointTerminal
  have selectorTerminal : Cont selectorRead (append provenance endpoint) terminalRead := by
    cases selectorProvenanceSeal
    exact sealEndpointTerminal.trans (append_assoc selectorRead provenance endpoint)
  have terminalSelectorNonescape :
      Cont terminalRead (BHist.e0 hostLimit) selectorRead -> False :=
    fun terminalSelector =>
      (cont_mutual_extension_right_tail_absurd.left selectorTerminal terminalSelector)
  have terminalSealNonescape :
      Cont terminalRead (BHist.e1 quotient) sealRead -> False :=
    fun terminalSeal =>
      (cont_mutual_extension_right_tail_absurd.right sealEndpointTerminal terminalSeal)
  exact
    ⟨selectorUnary, sealReadUnary, terminalReadUnary, ledgerRealSelector,
      selectorProvenanceSeal, sealEndpointTerminal, endpointPkg, terminalPkg,
      terminalSelectorNonescape, terminalSealNonescape⟩

end BEDC.Derived.CauchyCriterionUp
