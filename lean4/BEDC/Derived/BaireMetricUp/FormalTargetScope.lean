import BEDC.Derived.BaireMetricUp

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricFormalTargetScope [AskSetup] [PackageSetup]
    {S B W D R U H C P N _prefixRead radiusRead metricRead ultrametricRead
      formalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      Cont ultrametricRead R metricRead →
        Cont metricRead U formalRead →
          PkgSig bundle formalRead pkg →
            UnaryHistory radiusRead ∧ UnaryHistory ultrametricRead ∧
              UnaryHistory metricRead ∧ UnaryHistory formalRead ∧ Cont S B radiusRead ∧
                Cont radiusRead D ultrametricRead ∧ Cont ultrametricRead R metricRead ∧
                  Cont metricRead U formalRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle formalRead pkg := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier metricRoute formalRoute formalPkg
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, unaryR, unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, radiusRoute, ultrametricRoute, provenancePkg, _localNamePkg⟩ :=
    carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryS unaryB radiusRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary unaryD ultrametricRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed ultrametricUnary unaryR metricRoute
  have formalUnary : UnaryHistory formalRead :=
    unary_cont_closed metricUnary unaryU formalRoute
  exact
    ⟨radiusUnary, ultrametricUnary, metricUnary, formalUnary, radiusRoute, ultrametricRoute,
      metricRoute, formalRoute, provenancePkg, formalPkg⟩

end BEDC.Derived.BaireMetricUp
