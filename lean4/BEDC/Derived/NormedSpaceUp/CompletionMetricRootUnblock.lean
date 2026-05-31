import BEDC.Derived.NormedSpaceUp

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormedSpaceCarrier_completion_metric_root_unblock [AskSetup] [PackageSetup]
    {V R N M Q H T P C metricRead completionRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont N M metricRead ->
        Cont metricRead Q completionRead ->
          Cont completionRead H rootRead ->
            PkgSig bundle rootRead pkg ->
              UnaryHistory V ∧ UnaryHistory R ∧ UnaryHistory N ∧ UnaryHistory M ∧
                UnaryHistory Q ∧ UnaryHistory metricRead ∧ UnaryHistory completionRead ∧
                  UnaryHistory rootRead ∧ Cont N M metricRead ∧
                    Cont metricRead Q completionRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle C pkg ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: NormedSpaceCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier metricRoute completionRoute rootRoute rootPkg
  obtain ⟨vUnary, rUnary, nUnary, mUnary, qUnary, hUnary, _tUnary, _pUnary,
    _cUnary, _vectorNormRoute, _completionFacingRoute, _replayRoute, provenancePkg,
    localPkg⟩ := carrier
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed nUnary mUnary metricRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed metricReadUnary qUnary completionRoute
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed completionReadUnary hUnary rootRoute
  exact
    ⟨vUnary, rUnary, nUnary, mUnary, qUnary, metricReadUnary, completionReadUnary,
      rootReadUnary, metricRoute, completionRoute, provenancePkg, localPkg, rootPkg⟩

end BEDC.Derived.NormedSpaceUp
