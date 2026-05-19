import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_total_host_fuel_replay_boundary [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal replayRead ->
          PkgSig bundle replayRead pkg ->
            UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminalRead ∧
              UnaryHistory normal ∧ UnaryHistory replayRead ∧ hsame terminalRead terminal ∧
                Cont terminalRead normal replayRead ∧ Cont continuation transports routes ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalReplay replayPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalReplay
  exact
    ⟨typedUnary, fuelUnary, terminalReadUnary, normalUnary, replayReadUnary,
      terminalReadSame, terminalReadNormalReplay, continuationTransportsRoutes,
      provenancePkg, replayPkg⟩

end BEDC.Derived.ZnormalUp
