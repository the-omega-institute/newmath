import BEDC.Derived.ObserverRegularUp.Carrier

namespace BEDC.Derived.ObserverRegularUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverRegularCarrier_formal_target_boundary [AskSetup] [PackageSetup]
    {alphabet resolvingState schedule window readback transport route provenance name
      selectedWindow consumer handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverRegularCarrier alphabet resolvingState schedule window readback transport route
        provenance name bundle pkg →
      Cont resolvingState window selectedWindow →
        Cont selectedWindow readback consumer →
          Cont consumer provenance handoff →
            PkgSig bundle handoff pkg →
              UnaryHistory alphabet ∧
                UnaryHistory resolvingState ∧
                  UnaryHistory schedule ∧
                    UnaryHistory window ∧
                      UnaryHistory readback ∧
                        UnaryHistory transport ∧
                          UnaryHistory route ∧
                            UnaryHistory provenance ∧
                              UnaryHistory name ∧
                                UnaryHistory selectedWindow ∧
                                  UnaryHistory consumer ∧
                                    UnaryHistory handoff ∧
                                      Cont alphabet resolvingState schedule ∧
                                        Cont schedule window readback ∧
                                          Cont readback transport route ∧
                                            Cont route name provenance ∧
                                              Cont resolvingState window selectedWindow ∧
                                                Cont selectedWindow readback consumer ∧
                                                  Cont consumer provenance handoff ∧
                                                    PkgSig bundle provenance pkg ∧
                                                      PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier selectedRoute consumerRoute handoffRoute handoffPkg
  obtain ⟨alphabetUnary, resolvingStateUnary, scheduleUnary, windowUnary, readbackUnary,
    transportUnary, routeUnary, provenanceUnary, nameUnary, alphabetResolvingSchedule,
    scheduleWindowReadback, readbackTransportRoute, routeNameProvenance, provenancePkg,
    _semanticCert⟩ := carrier
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed resolvingStateUnary windowUnary selectedRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed selectedUnary readbackUnary consumerRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed consumerUnary provenanceUnary handoffRoute
  exact
    ⟨alphabetUnary,
      resolvingStateUnary,
      scheduleUnary,
      windowUnary,
      readbackUnary,
      transportUnary,
      routeUnary,
      provenanceUnary,
      nameUnary,
      selectedUnary,
      consumerUnary,
      handoffUnary,
      alphabetResolvingSchedule,
      scheduleWindowReadback,
      readbackTransportRoute,
      routeNameProvenance,
      selectedRoute,
      consumerRoute,
      handoffRoute,
      provenancePkg,
      handoffPkg⟩

end BEDC.Derived.ObserverRegularUp
