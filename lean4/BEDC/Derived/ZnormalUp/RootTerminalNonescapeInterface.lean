import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_terminal_nonescape_interface [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      terminalRoute consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal terminalRoute ->
          Cont terminalRoute transports consumer ->
            PkgSig bundle consumer pkg ->
              hsame terminalRead terminal ∧ hsame terminalRoute continuation ∧
                UnaryHistory terminalRead ∧ UnaryHistory terminalRoute ∧
                  UnaryHistory consumer ∧ Cont terminalRoute transports consumer ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet typedFuelTerminalRead terminalReadNormalTerminalRoute
    terminalRouteTransportsConsumer consumerPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalRouteSame : hsame terminalRoute continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal)
      terminalReadNormalTerminalRoute terminalNormalContinuation
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have terminalRouteUnary : UnaryHistory terminalRoute :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalTerminalRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed terminalRouteUnary transportsUnary terminalRouteTransportsConsumer
  exact
    ⟨terminalReadSame, terminalRouteSame, terminalReadUnary, terminalRouteUnary,
      consumerUnary, terminalRouteTransportsConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.ZnormalUp
