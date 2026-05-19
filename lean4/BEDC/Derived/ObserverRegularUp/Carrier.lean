import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObserverRegularUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ObserverRegularCarrier [AskSetup] [PackageSetup]
    (alphabet resolvingState schedule window readback transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory alphabet ∧ UnaryHistory resolvingState ∧ UnaryHistory schedule ∧
    UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont alphabet resolvingState schedule ∧ Cont schedule window readback ∧
          Cont readback transport route ∧ Cont route name provenance ∧
            PkgSig bundle provenance pkg ∧
              SemanticNameCert
                (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
                (fun row : BHist => hsame row provenance)
                (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
                hsame

theorem ObserverRegularCarrier_finite_ledger_non_escape [AskSetup] [PackageSetup]
    {alphabet resolvingState schedule window readback transport route provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverRegularCarrier alphabet resolvingState schedule window readback transport route
        provenance name bundle pkg ->
      Cont window readback consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory alphabet ∧ UnaryHistory resolvingState ∧ UnaryHistory window ∧
            UnaryHistory readback ∧ UnaryHistory consumer ∧ Cont window readback consumer ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  intro carrier consumerRow consumerPkg
  obtain ⟨alphabetUnary, resolvingStateUnary, _scheduleUnary, windowUnary, readbackUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _alphabetResolvingSchedule,
    _scheduleWindowReadback, _readbackTransportRoute, _routeNameProvenance, provenancePkg,
    _semanticCert⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed windowUnary readbackUnary consumerRow
  exact
    ⟨alphabetUnary, resolvingStateUnary, windowUnary, readbackUnary, consumerUnary,
      consumerRow, provenancePkg, consumerPkg⟩

theorem ObserverRegularCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {alphabet resolvingState schedule window readback transport route provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverRegularCarrier alphabet resolvingState schedule window readback transport route
        provenance name bundle pkg →
      Cont window readback consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory alphabet ∧ UnaryHistory resolvingState ∧ UnaryHistory schedule ∧
            UnaryHistory window ∧ UnaryHistory readback ∧ UnaryHistory transport ∧
              UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                Cont alphabet resolvingState schedule ∧ Cont schedule window readback ∧
                  Cont readback transport route ∧ Cont route name provenance ∧
                    Cont window readback consumer ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle consumer pkg ∧
                        SemanticNameCert
                          (fun row : BHist => hsame row provenance ∧ UnaryHistory row)
                          (fun row : BHist => hsame row provenance)
                          (fun row : BHist => hsame row provenance ∧
                            PkgSig bundle provenance pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame NameCert
  intro carrier consumerRoute consumerPkg
  obtain ⟨alphabetUnary, resolvingStateUnary, scheduleUnary, windowUnary, readbackUnary,
    transportUnary, routeUnary, provenanceUnary, nameUnary, alphabetResolvingSchedule,
    scheduleWindowReadback, readbackTransportRoute, routeNameProvenance, provenancePkg,
    semanticCert⟩ := carrier
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
      alphabetResolvingSchedule,
      scheduleWindowReadback,
      readbackTransportRoute,
      routeNameProvenance,
      consumerRoute,
      provenancePkg,
      consumerPkg,
      semanticCert⟩

theorem ObserverRegularCarrier_resolving_window_soundness [AskSetup] [PackageSetup]
    {alphabet resolvingState schedule window readback transport route provenance name
      selectedWindow consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverRegularCarrier alphabet resolvingState schedule window readback transport route
        provenance name bundle pkg ->
      Cont resolvingState window selectedWindow ->
        Cont selectedWindow readback consumer ->
          PkgSig bundle consumer pkg ->
            UnaryHistory resolvingState ∧ UnaryHistory window ∧ UnaryHistory selectedWindow ∧
              UnaryHistory readback ∧ UnaryHistory consumer ∧
                Cont alphabet resolvingState schedule ∧ Cont schedule window readback ∧
                  Cont resolvingState window selectedWindow ∧
                    Cont selectedWindow readback consumer ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier selectedRoute consumerRoute consumerPkg
  obtain ⟨_alphabetUnary, resolvingStateUnary, _scheduleUnary, windowUnary, readbackUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, alphabetResolvingSchedule,
    scheduleWindowReadback, _readbackTransportRoute, _routeNameProvenance, provenancePkg,
    _semanticCert⟩ := carrier
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed resolvingStateUnary windowUnary selectedRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed selectedUnary readbackUnary consumerRoute
  exact
    ⟨resolvingStateUnary,
      windowUnary,
      selectedUnary,
      readbackUnary,
      consumerUnary,
      alphabetResolvingSchedule,
      scheduleWindowReadback,
      selectedRoute,
      consumerRoute,
      provenancePkg,
      consumerPkg⟩

theorem ObserverRegularCarrier_streamname_handoff [AskSetup] [PackageSetup]
    {alphabet resolvingState schedule window readback transport route provenance name
      selectedWindow consumer handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverRegularCarrier alphabet resolvingState schedule window readback transport route
        provenance name bundle pkg ->
      Cont resolvingState window selectedWindow ->
        Cont selectedWindow readback consumer ->
          Cont consumer provenance handoff ->
            PkgSig bundle handoff pkg ->
              UnaryHistory selectedWindow ∧ UnaryHistory consumer ∧ UnaryHistory handoff ∧
                Cont selectedWindow readback consumer ∧ Cont consumer provenance handoff ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier selectedRoute consumerRoute handoffRoute handoffPkg
  obtain ⟨_alphabetUnary, resolvingStateUnary, _scheduleUnary, windowUnary, readbackUnary,
    _transportUnary, _routeUnary, provenanceUnary, _nameUnary, _alphabetResolvingSchedule,
    _scheduleWindowReadback, _readbackTransportRoute, _routeNameProvenance, provenancePkg,
    _semanticCert⟩ := carrier
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed resolvingStateUnary windowUnary selectedRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed selectedUnary readbackUnary consumerRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed consumerUnary provenanceUnary handoffRoute
  exact
    ⟨selectedUnary,
      consumerUnary,
      handoffUnary,
      consumerRoute,
      handoffRoute,
      provenancePkg,
      handoffPkg⟩

theorem ObserverRegularCarrier_schedule_lock_real_completion [AskSetup] [PackageSetup]
    {alphabet resolvingState schedule window readback transport route provenance name
      selectedWindow consumer handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverRegularCarrier alphabet resolvingState schedule window readback transport route
        provenance name bundle pkg →
      Cont resolvingState window selectedWindow →
        Cont selectedWindow readback consumer →
          Cont consumer provenance handoff →
            PkgSig bundle handoff pkg →
              UnaryHistory schedule ∧ UnaryHistory window ∧ UnaryHistory readback ∧
                UnaryHistory selectedWindow ∧ UnaryHistory consumer ∧ UnaryHistory handoff ∧
                  Cont alphabet resolvingState schedule ∧ Cont schedule window readback ∧
                    Cont selectedWindow readback consumer ∧ Cont consumer provenance handoff ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier selectedRoute consumerRoute handoffRoute handoffPkg
  obtain ⟨_alphabetUnary, resolvingStateUnary, scheduleUnary, windowUnary, readbackUnary,
    _transportUnary, _routeUnary, provenanceUnary, _nameUnary, alphabetResolvingSchedule,
    scheduleWindowReadback, _readbackTransportRoute, _routeNameProvenance, provenancePkg,
    _semanticCert⟩ := carrier
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed resolvingStateUnary windowUnary selectedRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed selectedUnary readbackUnary consumerRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed consumerUnary provenanceUnary handoffRoute
  exact
    ⟨scheduleUnary,
      windowUnary,
      readbackUnary,
      selectedUnary,
      consumerUnary,
      handoffUnary,
      alphabetResolvingSchedule,
      scheduleWindowReadback,
      consumerRoute,
      handoffRoute,
      provenancePkg,
      handoffPkg⟩

end BEDC.Derived.ObserverRegularUp
