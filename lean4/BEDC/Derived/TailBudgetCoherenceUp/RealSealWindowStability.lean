import BEDC.Derived.TailBudgetCoherenceUp

namespace BEDC.Derived.TailBudgetCoherenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailBudgetCoherenceCarrier_real_seal_window_stability [AskSetup] [PackageSetup]
    {meet observationBudget selectorBudget agreementSeal limitSeal window readback dyadic
      transport routes provenance localCert endpoint sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal limitSeal
        window readback dyadic transport routes provenance localCert endpoint bundle pkg ->
      Cont readback agreementSeal limitSeal ->
        Cont limitSeal transport routes ->
          PkgSig bundle sealRead pkg ->
            UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
              UnaryHistory agreementSeal ∧ UnaryHistory limitSeal ∧
                Cont readback agreementSeal limitSeal ∧ Cont limitSeal transport routes ∧
                  hsame endpoint (append provenance localCert) ∧ PkgSig bundle endpoint pkg ∧
                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier _readbackAgreementLimit _limitTransportRoutes sealReadPkg
  obtain ⟨_meetUnary, _observationUnary, _selectorUnary, agreementUnary, limitUnary,
    windowUnary, readbackUnary, dyadicUnary, _transportUnary, _routesUnary,
    _provenanceUnary, _localCertUnary, _endpointUnary, _meetObservationWindow,
    _meetSelectorDyadic, _windowDyadicReadback, readbackAgreementLimit,
    limitTransportRoutes, _routesProvenanceLocalCert, _provenanceLocalCertEndpoint,
    endpointSame, endpointPkg⟩ := carrier
  exact
    ⟨windowUnary, dyadicUnary, readbackUnary, agreementUnary, limitUnary,
      readbackAgreementLimit, limitTransportRoutes, endpointSame, endpointPkg,
      sealReadPkg⟩

end BEDC.Derived.TailBudgetCoherenceUp
