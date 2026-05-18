import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalTerminalBoundaryNonescape [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal readback →
          PkgSig bundle readback pkg →
            UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
              UnaryHistory normal ∧ UnaryHistory terminalRead ∧ UnaryHistory readback ∧
                Cont typed fuel terminalRead ∧ Cont terminalRead normal readback ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalReadback readbackPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalReadback
  exact
    ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, terminalReadUnary, readbackUnary,
      typedFuelTerminalRead, terminalReadNormalReadback, provenancePkg, readbackPkg⟩

end BEDC.Derived.ZnormalUp
