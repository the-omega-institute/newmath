import BEDC.Derived.TailBudgetCoherenceUp

namespace BEDC.Derived.TailBudgetCoherenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailBudgetCoherenceCarrier_synchronizer_comparison [AskSetup] [PackageSetup]
    {meet observationBudget selectorBudget agreementSeal limitSeal window readback dyadic
      transport routes provenance localCert endpoint synchronizerSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal limitSeal
        window readback dyadic transport routes provenance localCert endpoint bundle pkg ->
      Cont window readback synchronizerSeal ->
        PkgSig bundle synchronizerSeal pkg ->
          UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory synchronizerSeal ∧
            Cont window readback synchronizerSeal ∧ hsame endpoint (append provenance localCert) ∧
              PkgSig bundle endpoint pkg ∧ PkgSig bundle synchronizerSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory hsame
  intro carrier synchronizerRoute synchronizerPkg
  rcases carrier with
    ⟨_meetUnary, _observationBudgetUnary, _selectorBudgetUnary, _agreementSealUnary,
      _limitSealUnary, windowUnary, readbackUnary, _dyadicUnary, _transportUnary,
      _routesUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
      _meetObservationWindow, _meetSelectorDyadic, _windowDyadicReadback,
      _readbackAgreementLimit, _limitTransportRoutes, _routesProvenanceLocalCert,
      _provenanceLocalCertEndpoint, endpointAppend, endpointPkg⟩
  have synchronizerUnary : UnaryHistory synchronizerSeal :=
    unary_cont_closed windowUnary readbackUnary synchronizerRoute
  exact
    ⟨windowUnary, readbackUnary, synchronizerUnary, synchronizerRoute, endpointAppend,
      endpointPkg, synchronizerPkg⟩

end BEDC.Derived.TailBudgetCoherenceUp
