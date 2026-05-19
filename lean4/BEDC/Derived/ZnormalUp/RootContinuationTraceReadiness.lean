import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_continuation_trace_readiness [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      traceReady : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead continuation traceReady →
          PkgSig bundle traceReady pkg →
            hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
              UnaryHistory traceReady ∧ Cont terminalRead continuation traceReady ∧
                Cont terminal normal continuation ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle traceReady pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadContinuationTrace traceReadyPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have traceReadyUnary : UnaryHistory traceReady :=
    unary_cont_closed terminalReadUnary continuationUnary terminalReadContinuationTrace
  exact
    ⟨terminalReadSame, terminalReadUnary, traceReadyUnary, terminalReadContinuationTrace,
      terminalNormalContinuation, provenancePkg, traceReadyPkg⟩

end BEDC.Derived.ZnormalUp
