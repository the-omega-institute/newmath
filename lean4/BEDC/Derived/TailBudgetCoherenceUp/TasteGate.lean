import BEDC.Derived.TailBudgetCoherenceUp

namespace BEDC.Derived.TailBudgetCoherenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailBudgetCoherenceCarrier_seal_nonescape [AskSetup] [PackageSetup]
    {meet observationBudget selectorBudget agreementSeal limitSeal window readback dyadic transport
      routes provenance localCert endpoint sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal limitSeal window
        readback dyadic transport routes provenance localCert endpoint bundle pkg ->
      PkgSig bundle sealRead pkg ->
        UnaryHistory meet ∧ UnaryHistory observationBudget ∧ UnaryHistory selectorBudget ∧
          UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
            UnaryHistory agreementSeal ∧ UnaryHistory limitSeal ∧
              Cont meet observationBudget window ∧ Cont meet selectorBudget dyadic ∧
                Cont window dyadic readback ∧ Cont readback agreementSeal limitSeal ∧
                  Cont limitSeal transport routes ∧ hsame endpoint (append provenance localCert) ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro carrier sealReadPkg
  rcases carrier with
    ⟨meetUnary, observationBudgetUnary, selectorBudgetUnary, agreementSealUnary,
      limitSealUnary, windowUnary, readbackUnary, dyadicUnary, _transportUnary, _routesUnary,
      _provenanceUnary, _localCertUnary, _endpointUnary, meetObservationWindow,
      meetSelectorDyadic, windowDyadicReadback, readbackAgreementLimit, limitTransportRoutes,
      _routesProvenanceLocalCert, _provenanceLocalCertEndpoint, endpointAppend, endpointPkg⟩
  exact
    ⟨meetUnary, observationBudgetUnary, selectorBudgetUnary, windowUnary, dyadicUnary,
      readbackUnary, agreementSealUnary, limitSealUnary, meetObservationWindow,
      meetSelectorDyadic, windowDyadicReadback, readbackAgreementLimit, limitTransportRoutes,
      endpointAppend, endpointPkg, sealReadPkg⟩

end BEDC.Derived.TailBudgetCoherenceUp
