import BEDC.Derived.BaireMetricUp

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricPrefixRadiusTransport [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead radiusRead' ultrametricRead'
      metricRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      Cont S B radiusRead' →
        Cont radiusRead' D ultrametricRead' →
          Cont ultrametricRead' R metricRead' →
            PkgSig bundle metricRead' pkg →
              UnaryHistory radiusRead' ∧ UnaryHistory ultrametricRead' ∧
                UnaryHistory metricRead' ∧ Cont S B radiusRead' ∧
                  Cont radiusRead' D ultrametricRead' ∧
                    Cont ultrametricRead' R metricRead' ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle metricRead' pkg := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeRadius routeUltrametric routeMetric metricPkg
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, unaryR, _unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, _radiusRoute, _ultrametricRoute, provenancePkg, _localNamePkg⟩ :=
    carrier
  have radiusUnary : UnaryHistory radiusRead' :=
    unary_cont_closed unaryS unaryB routeRadius
  have ultrametricUnary : UnaryHistory ultrametricRead' :=
    unary_cont_closed radiusUnary unaryD routeUltrametric
  have metricUnary : UnaryHistory metricRead' :=
    unary_cont_closed ultrametricUnary unaryR routeMetric
  exact
    ⟨radiusUnary, ultrametricUnary, metricUnary, routeRadius, routeUltrametric, routeMetric,
      provenancePkg, metricPkg⟩

end BEDC.Derived.BaireMetricUp
