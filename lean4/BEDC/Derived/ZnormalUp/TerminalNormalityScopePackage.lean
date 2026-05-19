import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_normality_scope_package [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      terminalScope : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead continuation terminalScope →
          PkgSig bundle terminalScope pkg →
            hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
              UnaryHistory terminalScope ∧ Cont terminalRead continuation terminalScope ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle terminalScope pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadContinuationScope terminalScopePkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have terminalScopeUnary : UnaryHistory terminalScope :=
    unary_cont_closed terminalReadUnary continuationUnary terminalReadContinuationScope
  exact
    ⟨terminalReadSame, terminalReadUnary, terminalScopeUnary, terminalReadContinuationScope,
      provenancePkg, terminalScopePkg⟩

theorem ZnormalPacket_terminal_normality_consumer_gate [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead continuation consumer →
          PkgSig bundle consumer pkg →
            hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
              UnaryHistory consumer ∧ Cont typed fuel terminal ∧
                Cont terminal normal continuation ∧ Cont typed fuel terminalRead ∧
                  Cont terminalRead continuation consumer ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadContinuationConsumer consumerPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed terminalReadUnary continuationUnary terminalReadContinuationConsumer
  exact
    ⟨terminalReadSame, terminalReadUnary, consumerUnary, typedFuelTerminal,
      terminalNormalContinuation, typedFuelTerminalRead, terminalReadContinuationConsumer,
      provenancePkg, consumerPkg⟩

end BEDC.Derived.ZnormalUp
