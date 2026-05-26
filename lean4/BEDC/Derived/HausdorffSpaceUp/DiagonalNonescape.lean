import BEDC.Derived.HausdorffSpaceUp.TasteGate

namespace BEDC.Derived.HausdorffSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffSpaceCarrier_diagonal_nonescape [AskSetup] [PackageSetup]
    {T x y U V D M E H C P N pointRoute separation metricRoute realSealRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffSpaceCarrier T x y U V D M E H C P N bundle pkg ->
      Cont T x pointRoute -> Cont pointRoute y C -> Cont U V separation ->
        Cont M E metricRoute -> Cont metricRoute separation realSealRoute ->
          UnaryHistory T ∧ UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory U ∧
            UnaryHistory V ∧ UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory E ∧
              UnaryHistory pointRoute ∧ UnaryHistory separation ∧ UnaryHistory metricRoute ∧
                UnaryHistory realSealRoute ∧ Cont T x pointRoute ∧ Cont pointRoute y C ∧
                  Cont U V separation ∧ Cont M E metricRoute ∧
                    Cont metricRoute separation realSealRoute ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier topologyPoint pointClassifier neighborhoodSeparation metricReplay realSealReplay
  obtain ⟨tUnary, xUnary, yUnary, uUnary, vUnary, dUnary, mUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _carrierPointRoute, _carrierPointClassifier,
    _carrierSeparation, _carrierMetric, pPkg⟩ := carrier
  have pointRouteUnary : UnaryHistory pointRoute :=
    unary_cont_closed tUnary xUnary topologyPoint
  have separationUnary : UnaryHistory separation :=
    unary_cont_closed uUnary vUnary neighborhoodSeparation
  have metricRouteUnary : UnaryHistory metricRoute :=
    unary_cont_closed mUnary eUnary metricReplay
  have realSealRouteUnary : UnaryHistory realSealRoute :=
    unary_cont_closed metricRouteUnary separationUnary realSealReplay
  exact
    ⟨tUnary, xUnary, yUnary, uUnary, vUnary, dUnary, mUnary, eUnary, pointRouteUnary,
      separationUnary, metricRouteUnary, realSealRouteUnary, topologyPoint, pointClassifier,
      neighborhoodSeparation, metricReplay, realSealReplay, pPkg⟩

end BEDC.Derived.HausdorffSpaceUp
