import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_terminal_normality_exposure [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont fuel terminal terminalRead ->
        PkgSig bundle terminalRead pkg ->
          UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
            UnaryHistory continuation ∧ UnaryHistory terminalRead ∧
              Cont typed fuel terminal ∧ Cont fuel terminal terminalRead ∧
                Cont continuation transports routes ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet fuelTerminalRead terminalReadPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, continuationTransportsRoutes, namePkg, _provenancePkg⟩ :=
    packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed fuelUnary terminalUnary fuelTerminalRead
  exact
    ⟨typedUnary, fuelUnary, terminalUnary, continuationUnary, terminalReadUnary,
      typedFuelTerminal, fuelTerminalRead, continuationTransportsRoutes, namePkg,
      terminalReadPkg⟩

end BEDC.Derived.ZnormalUp
