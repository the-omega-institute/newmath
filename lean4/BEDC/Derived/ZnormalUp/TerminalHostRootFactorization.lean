import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_host_root_factorization [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      normalRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal normalRead ->
          Cont normalRead routes consumer ->
            PkgSig bundle consumer pkg ->
              hsame terminalRead terminal ∧ UnaryHistory normalRead ∧
                UnaryHistory consumer ∧ Cont typed fuel terminalRead ∧
                  Cont terminalRead normal normalRead ∧ Cont normalRead routes consumer ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalRead normalReadRoutesConsumer
    consumerPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have normalReadContinuation : hsame normalRead continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal) terminalReadNormalRead
      terminalNormalContinuation
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed normalReadUnary routesUnary normalReadRoutesConsumer
  exact
    ⟨terminalReadSame, normalReadUnary, consumerUnary, typedFuelTerminalRead,
      terminalReadNormalRead, normalReadRoutesConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.ZnormalUp
