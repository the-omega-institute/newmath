import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_carrier_total_host_readiness [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name
      totalHostRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel totalHostRead →
        PkgSig bundle totalHostRead pkg →
          UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
            UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory transports ∧
              UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                UnaryHistory totalHostRead ∧ Cont typed fuel terminal ∧
                  Cont typed fuel totalHostRead ∧ Cont terminal normal continuation ∧
                    Cont continuation transports routes ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle totalHostRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet typedFuelTotalHostRead totalHostReadPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have totalHostReadUnary : UnaryHistory totalHostRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTotalHostRead
  exact
    ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
      transportsUnary, routesUnary, provenanceUnary, nameUnary, totalHostReadUnary,
      typedFuelTerminal, typedFuelTotalHostRead, terminalNormalContinuation,
      continuationTransportsRoutes, provenancePkg, namePkg, totalHostReadPkg⟩

end BEDC.Derived.ZnormalUp
