import BEDC.Derived.ObserverRegularUp.Carrier

namespace BEDC.Derived.ObserverRegularUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverRegularCarrier_prefix_resolution_totality [AskSetup] [PackageSetup]
    {alphabet resolvingState schedule window readback transport route provenance name
      selectedWindow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverRegularCarrier alphabet resolvingState schedule window readback transport route
        provenance name bundle pkg →
      Cont resolvingState window selectedWindow →
        Cont selectedWindow readback consumer →
          PkgSig bundle consumer pkg →
            UnaryHistory alphabet ∧ UnaryHistory resolvingState ∧
              UnaryHistory selectedWindow ∧ UnaryHistory consumer ∧
                Cont resolvingState window selectedWindow ∧
                  Cont selectedWindow readback consumer ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier selectedRoute consumerRoute consumerPkg
  obtain ⟨alphabetUnary, resolvingStateUnary, _scheduleUnary, windowUnary, readbackUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _alphabetResolvingSchedule,
    _scheduleWindowReadback, _readbackTransportRoute, _routeNameProvenance, provenancePkg,
    _semanticCert⟩ := carrier
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed resolvingStateUnary windowUnary selectedRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed selectedUnary readbackUnary consumerRoute
  exact
    ⟨alphabetUnary, resolvingStateUnary, selectedUnary, consumerUnary, selectedRoute,
      consumerRoute, provenancePkg, consumerPkg⟩

end BEDC.Derived.ObserverRegularUp
