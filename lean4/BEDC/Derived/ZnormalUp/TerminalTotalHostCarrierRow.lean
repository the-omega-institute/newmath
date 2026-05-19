import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalTerminalTotalHostCarrierRow [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      normalRead carrierRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal normalRead →
          Cont normalRead continuation carrierRow →
            PkgSig bundle carrierRow pkg →
              hsame terminalRead terminal ∧ UnaryHistory normalRead ∧
                UnaryHistory carrierRow ∧ Cont terminalRead normal normalRead ∧
                  Cont normalRead continuation carrierRow ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle carrierRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalRead normalReadContinuationCarrier
    carrierPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRead
  have carrierRowUnary : UnaryHistory carrierRow :=
    unary_cont_closed normalReadUnary continuationUnary normalReadContinuationCarrier
  exact
    ⟨terminalReadSame, normalReadUnary, carrierRowUnary, terminalReadNormalRead,
      normalReadContinuationCarrier, provenancePkg, carrierPkg⟩

end BEDC.Derived.ZnormalUp
