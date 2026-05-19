import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_total_host_terminal_carrier_admission [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      terminalCarrier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal terminalCarrier →
          PkgSig bundle terminalCarrier pkg →
            hsame terminalRead terminal ∧ UnaryHistory terminalRead ∧
              UnaryHistory terminalCarrier ∧ Cont typed fuel terminalRead ∧
                Cont terminalRead normal terminalCarrier ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle terminalCarrier pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalCarrier terminalCarrierPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have terminalCarrierUnary : UnaryHistory terminalCarrier :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalCarrier
  exact
    ⟨terminalReadSame, terminalReadUnary, terminalCarrierUnary, typedFuelTerminalRead,
      terminalReadNormalCarrier, provenancePkg, terminalCarrierPkg⟩

end BEDC.Derived.ZnormalUp
