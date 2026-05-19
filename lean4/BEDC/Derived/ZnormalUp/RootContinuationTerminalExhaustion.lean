import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_continuation_terminal_exhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      continuationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal continuationRead →
          PkgSig bundle continuationRead pkg →
            hsame terminalRead terminal ∧ UnaryHistory typed ∧ UnaryHistory fuel ∧
              UnaryHistory terminalRead ∧ UnaryHistory normal ∧ UnaryHistory continuationRead ∧
                Cont typed fuel terminalRead ∧ Cont terminalRead normal continuationRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle continuationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalContinuationRead continuationReadPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have continuationReadUnary : UnaryHistory continuationRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalContinuationRead
  exact
    ⟨terminalReadSame, typedUnary, fuelUnary, terminalReadUnary, normalUnary,
      continuationReadUnary, typedFuelTerminalRead, terminalReadNormalContinuationRead,
      provenancePkg, continuationReadPkg⟩

end BEDC.Derived.ZnormalUp
