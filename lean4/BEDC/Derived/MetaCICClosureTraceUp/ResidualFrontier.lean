import BEDC.Derived.MetaCICClosureTraceUp

namespace BEDC.Derived.MetaCICClosureTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICClosureTraceCarrier_residual_frontier
    [AskSetup] [PackageSetup] {S U V B R G K H C P N residual frontier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICClosureTraceCarrier S U V B R G K H C P N bundle pkg ->
      Cont K C residual ->
        Cont residual N frontier ->
          PkgSig bundle frontier pkg ->
            UnaryHistory K /\ UnaryHistory residual /\ UnaryHistory frontier /\
              Cont K C residual /\ Cont residual N frontier /\ PkgSig bundle frontier pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier kernelResidual residualFrontier frontierPkg
  obtain ⟨_SUnary, _UUnary, _VUnary, _BUnary, _RUnary, _GUnary, KUnary, _HUnary,
    CUnary, _PUnary, NUnary, _shiftSubstitution, _generatorPackage, _betaRoute,
    _pkgSig⟩ := carrier
  have residualUnary : UnaryHistory residual :=
    unary_cont_closed KUnary CUnary kernelResidual
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed residualUnary NUnary residualFrontier
  exact
    ⟨KUnary, residualUnary, frontierUnary, kernelResidual, residualFrontier,
      frontierPkg⟩

end BEDC.Derived.MetaCICClosureTraceUp
