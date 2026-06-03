import BEDC.Derived.BaireMetricUp

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricRootPrefixUltrametricPackage [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead metricRead strongTriangleRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      Cont ultrametricRead R metricRead →
        Cont metricRead U strongTriangleRead →
          Cont strongTriangleRead N namedRead →
            PkgSig bundle namedRead pkg →
              UnaryHistory radiusRead ∧ UnaryHistory ultrametricRead ∧
                UnaryHistory metricRead ∧ UnaryHistory strongTriangleRead ∧
                  UnaryHistory namedRead ∧ Cont S B radiusRead ∧
                    Cont radiusRead D ultrametricRead ∧
                      Cont ultrametricRead R metricRead ∧
                        Cont metricRead U strongTriangleRead ∧
                          Cont strongTriangleRead N namedRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier metricRoute strongTriangleRoute namedRoute namedPkg
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, unaryR, unaryU, _unaryH, _unaryC,
    _unaryP, unaryN, radiusRoute, ultrametricRoute, provenancePkg, _localNamePkg⟩ :=
    carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryS unaryB radiusRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary unaryD ultrametricRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed ultrametricUnary unaryR metricRoute
  have strongTriangleUnary : UnaryHistory strongTriangleRead :=
    unary_cont_closed metricUnary unaryU strongTriangleRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed strongTriangleUnary unaryN namedRoute
  exact
    ⟨radiusUnary, ultrametricUnary, metricUnary, strongTriangleUnary, namedUnary,
      radiusRoute, ultrametricRoute, metricRoute, strongTriangleRoute, namedRoute,
      provenancePkg, namedPkg⟩

end BEDC.Derived.BaireMetricUp
