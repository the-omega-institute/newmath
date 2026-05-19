import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_readiness_terminal_nonescape [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead continuation downstream →
          PkgSig bundle downstream pkg →
            hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
              UnaryHistory downstream ∧ Cont typed fuel terminalRead ∧
                Cont terminalRead continuation downstream ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle downstream pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig UnaryHistory
  intro packet typedFuelTerminalRead terminalReadContinuationDownstream downstreamPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have sameTerminalRead : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed terminalReadUnary continuationUnary terminalReadContinuationDownstream
  exact
    ⟨sameTerminalRead, terminalReadUnary, downstreamUnary, typedFuelTerminalRead,
      terminalReadContinuationDownstream, provenancePkg, downstreamPkg⟩

end BEDC.Derived.ZnormalUp
