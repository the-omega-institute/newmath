import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_fuel_consumer_package [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      replayRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal replayRead ->
          Cont replayRead transports consumer ->
            PkgSig bundle consumer pkg ->
              hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
                UnaryHistory replayRead ∧ UnaryHistory consumer ∧
                  Cont terminalRead normal replayRead ∧ Cont replayRead transports consumer ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalReplay replayTransportsConsumer
    consumerPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg,
    provenancePkg⟩ := packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalReplay
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed replayReadUnary transportsUnary replayTransportsConsumer
  exact
    ⟨terminalReadSame, terminalReadUnary, replayReadUnary, consumerUnary,
      terminalReadNormalReplay, replayTransportsConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.ZnormalUp
