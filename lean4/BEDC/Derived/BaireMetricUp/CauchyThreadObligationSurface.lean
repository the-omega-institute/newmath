import BEDC.Derived.BaireMetricUp

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def BaireMetricCauchyThreadObligationSurface [AskSetup] [PackageSetup]
    (S B W D R U H C P N radiusRead ultrametricRead completeRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  BaireMetricPrefixDistanceCarrier S B W D R U H C P N radiusRead ultrametricRead
      bundle pkg ∧
    Cont ultrametricRead R completeRead ∧ PkgSig bundle completeRead pkg

end BEDC.Derived.BaireMetricUp
