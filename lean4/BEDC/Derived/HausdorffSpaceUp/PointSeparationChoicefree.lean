import BEDC.Derived.HausdorffSpaceUp.TasteGate

namespace BEDC.Derived.HausdorffSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffSpaceCarrier_point_separation_choicefree [AskSetup] [PackageSetup]
    {T x y U V D M E H C P N positiveDistance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffSpaceCarrier T x y U V D M E H C P N bundle pkg ->
      Cont M E positiveDistance ->
        UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory U ∧ UnaryHistory V ∧
          UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory E ∧
            UnaryHistory positiveDistance ∧ hsame positiveDistance C ∧ Cont U V D ∧
              PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier positiveDistanceRoute
  obtain ⟨_tUnary, xUnary, yUnary, uUnary, vUnary, dUnary, mUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _pointRoute, _transportRoute, disjointRoute, metricRoute,
    pkgRow⟩ := carrier
  have positiveDistanceUnary : UnaryHistory positiveDistance :=
    unary_cont_closed mUnary eUnary positiveDistanceRoute
  have positiveDistanceSame : hsame positiveDistance C :=
    cont_deterministic positiveDistanceRoute metricRoute
  exact
    ⟨xUnary, yUnary, uUnary, vUnary, dUnary, mUnary, eUnary, positiveDistanceUnary,
      positiveDistanceSame, disjointRoute, pkgRow⟩

end BEDC.Derived.HausdorffSpaceUp
