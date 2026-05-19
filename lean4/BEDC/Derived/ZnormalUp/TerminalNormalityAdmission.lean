import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalTerminalNormalityAdmission [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      normalityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel terminalRead ->
        Cont terminalRead normal normalityRead ->
          PkgSig bundle normalityRead pkg ->
            hsame terminalRead terminal ∧ UnaryHistory typed ∧ UnaryHistory fuel ∧
              UnaryHistory terminalRead ∧ UnaryHistory normal ∧ UnaryHistory normalityRead ∧
                Cont typed fuel terminalRead ∧ Cont terminalRead normal normalityRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle normalityRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalityRead normalityPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have normalityReadUnary : UnaryHistory normalityRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalityRead
  exact
    ⟨terminalReadSame, typedUnary, fuelUnary, terminalReadUnary, normalUnary,
      normalityReadUnary, typedFuelTerminalRead, terminalReadNormalityRead, provenancePkg,
      normalityPkg⟩

end BEDC.Derived.ZnormalUp
