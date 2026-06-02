import BEDC.Derived.IshiharaTrickUp

namespace BEDC.Derived.IshiharaTrickUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IshiharaTrickCarrier_finite_test_boundary [AskSetup] [PackageSetup]
    {S R T W D E A H C P N branch : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IshiharaTrickCarrier S R T W D E A H C P N bundle pkg ->
      Cont T W branch ->
        PkgSig bundle branch pkg ->
          UnaryHistory T ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory branch ∧
            Cont T W branch ∧ Cont W D A ∧ PkgSig bundle P pkg ∧
              PkgSig bundle branch pkg := by
  -- BEDC touchpoint anchor: IshiharaTrickCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier branchRoute branchPkg
  obtain ⟨_SUnary, _RUnary, TUnary, WUnary, DUnary, _EUnary, _AUnary, _HUnary,
    _CUnary, _PUnary, _NUnary, _scheduleRoute, windowBoundary, _testRoute, _replayRoute,
    provenancePkg, _namePkg⟩ := carrier
  have branchUnary : UnaryHistory branch :=
    unary_cont_closed TUnary WUnary branchRoute
  exact
    ⟨TUnary, WUnary, DUnary, branchUnary, branchRoute, windowBoundary, provenancePkg,
      branchPkg⟩

end BEDC.Derived.IshiharaTrickUp
