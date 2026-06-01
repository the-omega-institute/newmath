import BEDC.Derived.NormedSpaceUp

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormedspaceMetricCompletionUnblock [AskSetup] [PackageSetup]
    {V R N M Q H T P C metricRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg →
      Cont V N metricRead →
        Cont metricRead Q completionRead →
          PkgSig bundle completionRead pkg →
            UnaryHistory metricRead ∧ UnaryHistory completionRead ∧
              Cont V N metricRead ∧ Cont metricRead Q completionRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: NormedSpaceCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier metricRoute completionRoute completionPkg
  obtain ⟨vUnary, _rUnary, nUnary, _mUnary, qUnary, _hUnary, _tUnary, _pUnary,
    _cUnary, _vectorNormRoute, _completionFacingRoute, _replayRoute, provenancePkg,
    _localPkg⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed vUnary nUnary metricRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary qUnary completionRoute
  exact
    ⟨metricUnary, completionUnary, metricRoute, completionRoute, provenancePkg,
      completionPkg⟩

end BEDC.Derived.NormedSpaceUp
