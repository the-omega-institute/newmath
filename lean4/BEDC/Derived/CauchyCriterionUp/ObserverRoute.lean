import BEDC.Derived.CauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_tail_budget_observer_route [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      streamWindow tailRadius sharedThreshold observerRead observedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      UnaryHistory streamWindow ->
        Cont window streamWindow tailRadius ->
          Cont tailRadius ledger sharedThreshold ->
            Cont sharedThreshold realSeal observerRead ->
              Cont observerRead route observedEndpoint ->
                PkgSig bundle observedEndpoint pkg ->
                  UnaryHistory window ∧ UnaryHistory streamWindow ∧ UnaryHistory tailRadius ∧
                    UnaryHistory ledger ∧ UnaryHistory sharedThreshold ∧ UnaryHistory realSeal ∧
                      UnaryHistory observerRead ∧ UnaryHistory observedEndpoint ∧
                        Cont window streamWindow tailRadius ∧
                          Cont tailRadius ledger sharedThreshold ∧
                            Cont sharedThreshold realSeal observerRead ∧
                              Cont observerRead route observedEndpoint ∧
                                PkgSig bundle endpoint pkg ∧
                                  PkgSig bundle observedEndpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier streamWindowUnary windowStreamTail tailLedgerThreshold thresholdObserver
    observerRoute observedPkg
  obtain ⟨windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, routeUnary, _provenanceUnary, _localCertUnary,
    _endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := carrier
  have tailRadiusUnary : UnaryHistory tailRadius :=
    unary_cont_closed windowUnary streamWindowUnary windowStreamTail
  have sharedThresholdUnary : UnaryHistory sharedThreshold :=
    unary_cont_closed tailRadiusUnary ledgerUnary tailLedgerThreshold
  have observerReadUnary : UnaryHistory observerRead :=
    unary_cont_closed sharedThresholdUnary realSealUnary thresholdObserver
  have observedEndpointUnary : UnaryHistory observedEndpoint :=
    unary_cont_closed observerReadUnary routeUnary observerRoute
  exact
    ⟨windowUnary, streamWindowUnary, tailRadiusUnary, ledgerUnary, sharedThresholdUnary,
      realSealUnary, observerReadUnary, observedEndpointUnary, windowStreamTail,
      tailLedgerThreshold, thresholdObserver, observerRoute, endpointPkg, observedPkg⟩

end BEDC.Derived.CauchyCriterionUp
