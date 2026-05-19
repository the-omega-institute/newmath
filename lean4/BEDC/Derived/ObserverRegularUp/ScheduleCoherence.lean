import BEDC.Derived.ObserverRegularUp.Carrier

namespace BEDC.Derived.ObserverRegularUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverRegularCarrier_schedule_coherence [AskSetup] [PackageSetup]
    {alphabet resolvingState schedule window readback transport route provenance name
      alphabet' resolvingState' schedule' window' readback' transport' route' provenance' name'
      coherentSchedule coherentReadback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverRegularCarrier alphabet resolvingState schedule window readback transport route
        provenance name bundle pkg ->
      ObserverRegularCarrier alphabet' resolvingState' schedule' window' readback' transport'
        route' provenance' name' bundle pkg ->
        Cont schedule schedule' coherentSchedule ->
          Cont coherentSchedule readback coherentReadback ->
            PkgSig bundle coherentReadback pkg ->
              UnaryHistory schedule ∧ UnaryHistory schedule' ∧
                UnaryHistory coherentSchedule ∧ UnaryHistory coherentReadback ∧
                  Cont schedule schedule' coherentSchedule ∧
                    Cont coherentSchedule readback coherentReadback ∧
                      PkgSig bundle provenance pkg ∧
                        PkgSig bundle coherentReadback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier carrier' scheduleCoherence readbackCoherence coherentPkg
  obtain ⟨_alphabetUnary, _resolvingStateUnary, scheduleUnary, _windowUnary, readbackUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _alphabetResolvingSchedule,
    _scheduleWindowReadback, _readbackTransportRoute, _routeNameProvenance, provenancePkg,
    _semanticCert⟩ := carrier
  obtain ⟨_alphabetUnary', _resolvingStateUnary', scheduleUnary', _windowUnary',
    _readbackUnary', _transportUnary', _routeUnary', _provenanceUnary', _nameUnary',
    _alphabetResolvingSchedule', _scheduleWindowReadback', _readbackTransportRoute',
    _routeNameProvenance', _provenancePkg', _semanticCert'⟩ := carrier'
  have coherentScheduleUnary : UnaryHistory coherentSchedule :=
    unary_cont_closed scheduleUnary scheduleUnary' scheduleCoherence
  have coherentReadbackUnary : UnaryHistory coherentReadback :=
    unary_cont_closed coherentScheduleUnary readbackUnary readbackCoherence
  exact
    ⟨scheduleUnary,
      scheduleUnary',
      coherentScheduleUnary,
      coherentReadbackUnary,
      scheduleCoherence,
      readbackCoherence,
      provenancePkg,
      coherentPkg⟩

end BEDC.Derived.ObserverRegularUp
