import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_consumer_readiness [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead rootRead
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal rootRead ->
          Cont rootRead routes consumer ->
            PkgSig bundle consumer pkg ->
              hsame terminalRead terminal ∧ hsame rootRead continuation ∧
                UnaryHistory terminalRead ∧ UnaryHistory rootRead ∧ UnaryHistory consumer ∧
                  Cont typed fuel terminalRead ∧ Cont terminalRead normal rootRead ∧
                    Cont rootRead routes consumer ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalRootRead rootReadRoutesConsumer consumerPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have rootReadSame : hsame rootRead continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal) terminalReadNormalRootRead
      terminalNormalContinuation
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRootRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed rootReadUnary routesUnary rootReadRoutesConsumer
  exact
    ⟨terminalReadSame, rootReadSame, terminalReadUnary, rootReadUnary, consumerUnary,
      typedFuelTerminalRead, terminalReadNormalRootRead, rootReadRoutesConsumer, provenancePkg,
      consumerPkg⟩

end BEDC.Derived.ZnormalUp
