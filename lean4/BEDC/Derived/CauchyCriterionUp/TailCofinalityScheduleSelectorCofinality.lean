import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.TailCofinalityScheduleUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_tailcofinalityschedule_selector_cofinality
    [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      scheduleSource scheduleWindow scheduleDyadic scheduleRegseq scheduleSeal scheduleTransport
      scheduleRoute scheduleProvenance scheduleName scheduleEndpoint selector cauchySeal
      scheduleSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      BEDC.Derived.TailCofinalityScheduleUp.TailCofinalityScheduleCarrier scheduleSource
        scheduleWindow scheduleDyadic scheduleRegseq scheduleSeal scheduleTransport scheduleRoute
        scheduleProvenance scheduleName scheduleEndpoint bundle pkg ->
        hsame ledger scheduleDyadic ->
          hsame realSeal scheduleSeal ->
            Cont endpoint realSeal selector ->
              Cont ledger realSeal cauchySeal ->
                Cont scheduleDyadic scheduleSeal scheduleSealRead ->
                  PkgSig bundle selector pkg ->
                    PkgSig bundle cauchySeal pkg ->
                      PkgSig bundle scheduleSealRead pkg ->
                        UnaryHistory endpoint ∧ UnaryHistory selector ∧
                          UnaryHistory cauchySeal ∧ UnaryHistory scheduleSealRead ∧
                            hsame cauchySeal scheduleSealRead ∧
                              Cont endpoint realSeal selector ∧
                                Cont ledger realSeal cauchySeal ∧
                                  Cont scheduleDyadic scheduleSeal scheduleSealRead ∧
                                    PkgSig bundle endpoint pkg ∧
                                      PkgSig bundle selector pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro cauchy schedule sameLedger sameRealSeal endpointSelector ledgerSeal scheduleSealRoute
    selectorPkg _cauchyPkg _scheduleSealPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    endpointPkg⟩ := cauchy
  obtain ⟨_scheduleSourceUnary, _scheduleWindowUnary, scheduleDyadicUnary,
    _scheduleRegseqUnary, scheduleSealUnary, _scheduleTransportUnary, _scheduleRouteUnary,
    _scheduleProvenanceUnary, _scheduleNameUnary, _scheduleEndpointUnary,
    _scheduleSourceWindowDyadic, _scheduleDyadicRegseqSeal, _scheduleSealTransportRoute,
    _scheduleRouteProvenanceEndpoint, _scheduleEndpointName, _scheduleEndpointPkg⟩ :=
    schedule
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed endpointUnary realSealUnary endpointSelector
  have cauchySealUnary : UnaryHistory cauchySeal :=
    unary_cont_closed ledgerUnary realSealUnary ledgerSeal
  have scheduleSealReadUnary : UnaryHistory scheduleSealRead :=
    unary_cont_closed scheduleDyadicUnary scheduleSealUnary scheduleSealRoute
  have sameSealRead : hsame cauchySeal scheduleSealRead :=
    cont_respects_hsame sameLedger sameRealSeal ledgerSeal scheduleSealRoute
  exact
    ⟨endpointUnary, selectorUnary, cauchySealUnary, scheduleSealReadUnary, sameSealRead,
      endpointSelector, ledgerSeal, scheduleSealRoute, endpointPkg, selectorPkg⟩

end BEDC.Derived.CauchyCriterionUp
