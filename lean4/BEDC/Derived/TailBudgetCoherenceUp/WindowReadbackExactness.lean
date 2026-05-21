import BEDC.Derived.TailBudgetCoherenceUp

namespace BEDC.Derived.TailBudgetCoherenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailBudgetCoherenceCarrier_window_readback_exactness [AskSetup] [PackageSetup]
    {meet observationBudget selectorBudget agreementSeal limitSeal window readback dyadic
      transport routes provenance localCert endpoint window' dyadic' readback' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal limitSeal
        window readback dyadic transport routes provenance localCert endpoint bundle pkg ->
      Cont meet observationBudget window' ->
        Cont meet selectorBudget dyadic' ->
          Cont window' dyadic' readback' ->
            hsame window' window ∧ hsame dyadic' dyadic ∧ hsame readback' readback ∧
              UnaryHistory readback' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier altWindow altDyadic altReadback
  obtain ⟨meetUnary, observationBudgetUnary, selectorBudgetUnary, _agreementSealUnary,
    _limitSealUnary, _windowUnary, _readbackUnary, _dyadicUnary, _transportUnary,
    _routesUnary, _provenanceUnary, _localCertUnary, _endpointUnary, meetObservationWindow,
    meetSelectorDyadic, windowDyadicReadback, _readbackAgreementLimit,
    _limitTransportRoutes, _routesProvenanceLocal, _provenanceLocalEndpoint,
    _sameEndpoint, _endpointPkg⟩ := carrier
  have sameWindow : hsame window' window :=
    cont_deterministic altWindow meetObservationWindow
  have sameDyadic : hsame dyadic' dyadic :=
    cont_deterministic altDyadic meetSelectorDyadic
  have sameReadback : hsame readback' readback :=
    cont_respects_hsame sameWindow sameDyadic altReadback windowDyadicReadback
  have altWindowUnary : UnaryHistory window' :=
    unary_cont_closed meetUnary observationBudgetUnary altWindow
  have altDyadicUnary : UnaryHistory dyadic' :=
    unary_cont_closed meetUnary selectorBudgetUnary altDyadic
  have altReadbackUnary : UnaryHistory readback' :=
    unary_cont_closed altWindowUnary altDyadicUnary altReadback
  exact ⟨sameWindow, sameDyadic, sameReadback, altReadbackUnary⟩

end BEDC.Derived.TailBudgetCoherenceUp
