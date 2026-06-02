import BEDC.Derived.BaireMetricUp

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BaireMetricRootStreamNamePrefixRoute [AskSetup] [PackageSetup]
    {S B W D R U H C P N prefixRead radiusRead ultrametricRead scheduledRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
        bundle pkg →
      Cont S B prefixRead →
        Cont prefixRead W scheduledRead →
          PkgSig bundle scheduledRead pkg →
            UnaryHistory S ∧ UnaryHistory B ∧ UnaryHistory W ∧
              UnaryHistory prefixRead ∧ UnaryHistory scheduledRead ∧
                Cont S B prefixRead ∧ Cont prefixRead W scheduledRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle scheduledRead pkg := by
  -- BEDC touchpoint anchor: BaireMetricPrefixDistanceCarrier BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier prefixRoute scheduledRoute scheduledPkg
  obtain ⟨unaryS, unaryB, unaryW, _unaryD, _unaryR, _unaryU, _unaryH, _unaryC,
    _unaryP, _unaryN, _radiusRoute, _ultrametricRoute, provenancePkg, _localNamePkg⟩ :=
    carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryS unaryB prefixRoute
  have scheduledUnary : UnaryHistory scheduledRead :=
    unary_cont_closed prefixUnary unaryW scheduledRoute
  exact
    ⟨unaryS, unaryB, unaryW, prefixUnary, scheduledUnary, prefixRoute,
      scheduledRoute, provenancePkg, scheduledPkg⟩

end BEDC.Derived.BaireMetricUp
