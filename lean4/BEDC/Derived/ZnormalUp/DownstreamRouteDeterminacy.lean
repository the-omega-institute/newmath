import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_total_host_terminal_fuel_determinacy [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      terminalRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont typed fuel terminalRead' ->
          PkgSig bundle terminalRead pkg ->
            PkgSig bundle terminalRead' pkg ->
              hsame terminalRead terminalRead' ∧ hsame terminalRead terminal ∧
                UnaryHistory terminalRead ∧ UnaryHistory terminalRead' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet typedFuelTerminalRead typedFuelTerminalRead' _terminalReadPkg
    _terminalReadPkg'
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, _normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadSame' : hsame terminalRead' terminal :=
    cont_deterministic typedFuelTerminalRead' typedFuelTerminal
  have terminalReadsSame : hsame terminalRead terminalRead' :=
    hsame_trans terminalReadSame (hsame_symm terminalReadSame')
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have terminalReadUnary' : UnaryHistory terminalRead' :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead'
  exact ⟨terminalReadsSame, terminalReadSame, terminalReadUnary, terminalReadUnary'⟩

end BEDC.Derived.ZnormalUp
