import BEDC.Derived.BaireMetricUp

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricObligationClosureRoute [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead metricRead strongRead completeRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg ->
      Cont ultrametricRead R metricRead ->
        Cont metricRead U strongRead ->
          Cont strongRead C completeRead ->
            Cont completeRead N publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory radiusRead ∧ UnaryHistory ultrametricRead ∧
                  UnaryHistory metricRead ∧ UnaryHistory strongRead ∧
                    UnaryHistory completeRead ∧ UnaryHistory publicRead ∧
                      Cont S B radiusRead ∧ Cont radiusRead D ultrametricRead ∧
                        Cont ultrametricRead R metricRead ∧
                          Cont metricRead U strongRead ∧
                            Cont strongRead C completeRead ∧
                              Cont completeRead N publicRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist Cont ProbeBundle Pkg
  intro carrier metricRoute strongRoute completeRoute publicRoute publicPkg
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, unaryR, unaryU, _unaryH, unaryC,
    _unaryP, unaryN, radiusRoute, ultrametricRoute, provenancePkg, _localNamePkg⟩ :=
    carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed unaryS unaryB radiusRoute
  have ultrametricUnary : UnaryHistory ultrametricRead :=
    unary_cont_closed radiusUnary unaryD ultrametricRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed ultrametricUnary unaryR metricRoute
  have strongUnary : UnaryHistory strongRead :=
    unary_cont_closed metricUnary unaryU strongRoute
  have completeUnary : UnaryHistory completeRead :=
    unary_cont_closed strongUnary unaryC completeRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed completeUnary unaryN publicRoute
  exact
    ⟨radiusUnary, ultrametricUnary, metricUnary, strongUnary, completeUnary, publicUnary,
      radiusRoute, ultrametricRoute, metricRoute, strongRoute, completeRoute, publicRoute,
      provenancePkg, publicPkg⟩

end BEDC.Derived.BaireMetricUp
