import BEDC.Derived.TailBudgetCoherenceUp

namespace BEDC.Derived.TailBudgetCoherenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TailBudgetCoherenceCarrier_real_route_scope [AskSetup] [PackageSetup]
    {meet observationBudget selectorBudget agreementSeal limitSeal window readback dyadic
      transport routes provenance localCert endpoint realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailBudgetCoherenceCarrier meet observationBudget selectorBudget agreementSeal limitSeal
        window readback dyadic transport routes provenance localCert endpoint bundle pkg →
      Cont endpoint localCert realRead →
        UnaryHistory meet ∧ UnaryHistory observationBudget ∧ UnaryHistory selectorBudget ∧
          UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
            UnaryHistory agreementSeal ∧ UnaryHistory limitSeal ∧ UnaryHistory realRead ∧
              Cont meet observationBudget window ∧ Cont meet selectorBudget dyadic ∧
                Cont window dyadic readback ∧ Cont readback agreementSeal limitSeal ∧
                  Cont endpoint localCert realRead ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier endpointLocalCertReal
  obtain ⟨meetUnary, observationBudgetUnary, selectorBudgetUnary, agreementSealUnary,
    limitSealUnary, windowUnary, readbackUnary, dyadicUnary, _transportUnary, _routesUnary,
    _provenanceUnary, localCertUnary, endpointUnary, meetObservationWindow, meetSelectorDyadic,
    windowDyadicReadback, readbackAgreementLimit, _limitTransportRoutes,
    _routesProvenanceLocal, _provenanceLocalEndpoint, _endpointSame, endpointPkg⟩ := carrier
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed endpointUnary localCertUnary endpointLocalCertReal
  exact
    ⟨meetUnary, observationBudgetUnary, selectorBudgetUnary, windowUnary, dyadicUnary,
      readbackUnary, agreementSealUnary, limitSealUnary, realReadUnary, meetObservationWindow,
      meetSelectorDyadic, windowDyadicReadback, readbackAgreementLimit, endpointLocalCertReal,
      endpointPkg⟩

end BEDC.Derived.TailBudgetCoherenceUp
