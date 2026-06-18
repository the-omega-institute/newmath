import BEDC.Derived.BaireMetricUp

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BaireMetricRefinementSpine : BHist -> List BHist -> BHist -> Prop
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  | publicRead, [], refinedRead =>
      hsame refinedRead publicRead ∧ UnaryHistory refinedRead
  | publicRead, step :: tail, refinedRead =>
      ∃ prior : BHist,
        BaireMetricRefinementSpine publicRead tail prior ∧ UnaryHistory step ∧
          Cont prior step refinedRead

theorem BaireMetricCylindricalRefinementInduction [AskSetup] [PackageSetup]
    {S B W D R U H C P N radiusRead ultrametricRead metricRead strongRead completeRead
      publicRead refinedRead : BHist}
    {spine : List BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg ->
      Cont ultrametricRead R metricRead -> Cont metricRead U strongRead ->
        Cont strongRead C completeRead -> Cont completeRead N publicRead ->
          BaireMetricRefinementSpine publicRead spine refinedRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory refinedRead ∧
                BaireMetricRefinementSpine publicRead spine refinedRead ∧
                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro carrier metricRoute strongRoute completeRoute publicRoute spineRoute publicPkg
  obtain ⟨unaryS, unaryB, _unaryW, unaryD, unaryR, unaryU, _unaryH, unaryC,
    _unaryP, unaryN, radiusRoute, ultrametricRoute, _provenancePkg, _localNamePkg⟩ :=
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
  have refinedUnary :
      ∀ {tail : List BHist} {out : BHist},
        BaireMetricRefinementSpine publicRead tail out -> UnaryHistory out := by
    intro tail
    induction tail with
    | nil =>
        intro out hsp
        exact hsp.right
    | cons step rest ih =>
        intro out hsp
        obtain ⟨prior, priorSpine, stepUnary, stepRoute⟩ := hsp
        have priorUnary : UnaryHistory prior := ih priorSpine
        exact unary_cont_closed priorUnary stepUnary stepRoute
  exact ⟨refinedUnary spineRoute, spineRoute, publicPkg⟩

end BEDC.Derived.BaireMetricUp
