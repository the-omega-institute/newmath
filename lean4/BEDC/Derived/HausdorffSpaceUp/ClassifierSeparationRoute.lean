import BEDC.Derived.HausdorffSpaceUp.TasteGate

namespace BEDC.Derived.HausdorffSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HausdorffSpaceCarrier_classifier_separation_route [AskSetup] [PackageSetup]
    {T x y U V D M E H C P N separation metricRoute realSealRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffSpaceCarrier T x y U V D M E H C P N bundle pkg ->
      Cont T U C ->
        Cont V D separation ->
          Cont M E metricRoute ->
            Cont metricRoute separation realSealRoute ->
              UnaryHistory T ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory D ∧
                UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory metricRoute ∧
                  UnaryHistory realSealRoute ∧ Cont T U C ∧ Cont V D separation ∧
                    Cont M E metricRoute ∧ Cont metricRoute separation realSealRoute ∧
                      PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier openRoute separationRoute metricRouteRow realSealRouteRow
  obtain ⟨tUnary, _xUnary, _yUnary, uUnary, vUnary, dUnary, mUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _pointRoute, _transportRoute, _disjointRoute,
    _metricRoute, pkgRow⟩ := carrier
  have separationUnary : UnaryHistory separation :=
    unary_cont_closed vUnary dUnary separationRoute
  have metricRouteUnary : UnaryHistory metricRoute :=
    unary_cont_closed mUnary eUnary metricRouteRow
  have realSealRouteUnary : UnaryHistory realSealRoute :=
    unary_cont_closed metricRouteUnary separationUnary realSealRouteRow
  exact
    ⟨tUnary, uUnary, vUnary, dUnary, mUnary, eUnary, metricRouteUnary,
      realSealRouteUnary, openRoute, separationRoute, metricRouteRow, realSealRouteRow,
      pkgRow⟩

end BEDC.Derived.HausdorffSpaceUp
