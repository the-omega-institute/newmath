import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalFuelReplayNondivergenceBoundary [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal replayRead →
          PkgSig bundle replayRead pkg →
            hsame terminalRead terminal ∧ UnaryHistory fuel ∧ UnaryHistory terminalRead ∧
              UnaryHistory replayRead ∧ Cont typed fuel terminalRead ∧
                Cont terminalRead normal replayRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalReplay replayPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalReplay
  exact
    ⟨terminalReadSame, fuelUnary, terminalReadUnary, replayReadUnary,
      typedFuelTerminalRead, terminalReadNormalReplay, provenancePkg, replayPkg⟩

end BEDC.Derived.ZnormalUp
