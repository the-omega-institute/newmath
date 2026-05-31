import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_continuation_trace_boundary [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      traceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead continuation traceRead ->
          PkgSig bundle traceRead pkg ->
            hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
              UnaryHistory traceRead ∧ Cont typed fuel terminalRead ∧
                Cont terminalRead continuation traceRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle traceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadContinuationTrace tracePkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed terminalReadUnary continuationUnary terminalReadContinuationTrace
  exact
    ⟨terminalReadSame, terminalReadUnary, traceReadUnary, typedFuelTerminalRead,
      terminalReadContinuationTrace, provenancePkg, tracePkg⟩

end BEDC.Derived.ZnormalUp
