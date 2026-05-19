import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_total_host_field_readiness [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      refusalRead readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal refusalRead →
          Cont refusalRead continuation readback →
            PkgSig bundle readback pkg →
              hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
                UnaryHistory refusalRead ∧ UnaryHistory readback ∧
                  Cont typed fuel terminalRead ∧ Cont terminalRead normal refusalRead ∧
                    Cont refusalRead continuation readback ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalRefusal
    refusalContinuationReadback readbackPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRefusal
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed refusalReadUnary continuationUnary refusalContinuationReadback
  exact
    ⟨terminalReadSame, terminalReadUnary, refusalReadUnary, readbackUnary,
      typedFuelTerminalRead, terminalReadNormalRefusal, refusalContinuationReadback,
      provenancePkg, readbackPkg⟩

end BEDC.Derived.ZnormalUp
