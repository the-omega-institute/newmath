import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootKernelSourceTotality [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name source : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed routes source ->
        PkgSig bundle source pkg ->
          UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
            UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory transports ∧
              UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                UnaryHistory source ∧ Cont typed routes source ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle source pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet typedRoutesSource sourcePkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed typedUnary routesUnary typedRoutesSource
  exact
    ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
      transportsUnary, routesUnary, provenanceUnary, nameUnary, sourceUnary,
      typedRoutesSource, provenancePkg, sourcePkg⟩

end BEDC.Derived.ZnormalUp
