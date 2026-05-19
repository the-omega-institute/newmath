import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_fuel_replay_classifier_row [AskSetup] [PackageSetup]
    {typedEndpoint fuel terminal normal continuation transports routes provenance name
      fuelNormal replayOut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typedEndpoint fuel terminal normal continuation transports routes provenance name
      bundle pkg ->
    Cont fuel normal fuelNormal ->
    Cont fuelNormal continuation replayOut ->
    PkgSig bundle replayOut pkg ->
      UnaryHistory fuel ∧ UnaryHistory normal ∧ UnaryHistory continuation ∧
        UnaryHistory fuelNormal ∧ UnaryHistory replayOut ∧ Cont fuel normal fuelNormal ∧
          Cont fuelNormal continuation replayOut ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle replayOut pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet fuelNormalRoute replayRoute replayPkg
  obtain ⟨_typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have fuelNormalUnary : UnaryHistory fuelNormal :=
    unary_cont_closed fuelUnary normalUnary fuelNormalRoute
  have replayUnary : UnaryHistory replayOut :=
    unary_cont_closed fuelNormalUnary continuationUnary replayRoute
  exact
    ⟨fuelUnary, normalUnary, continuationUnary, fuelNormalUnary, replayUnary,
      fuelNormalRoute, replayRoute, provenancePkg, replayPkg⟩

end BEDC.Derived.ZnormalUp
