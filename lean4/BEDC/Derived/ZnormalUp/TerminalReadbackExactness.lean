import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalTerminalReadbackExactness [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
        Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
          Cont continuation transports routes ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro packet
  obtain ⟨typedUnary, fuelUnary, terminalUnary, _normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  exact
    ⟨typedUnary, fuelUnary, terminalUnary, typedFuelTerminal, terminalNormalContinuation,
      continuationTransportsRoutes, provenancePkg⟩

end BEDC.Derived.ZnormalUp
