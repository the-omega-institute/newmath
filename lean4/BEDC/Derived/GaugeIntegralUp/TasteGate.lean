import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived.GaugeIntegralUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def GaugeIntegralCarrier [AskSetup] [PackageSetup]
    (I Gamma T S D Q R H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  Cont I Gamma T ∧
    Cont T S D ∧
      Cont D Q R ∧
        Cont R H C ∧
          hsame N N ∧
            PkgSig bundle P pkg

def GaugeIntegralRoute [AskSetup] [PackageSetup]
    (I Gamma T S D Q R H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  GaugeIntegralCarrier I Gamma T S D Q R H C P N bundle pkg ∧
    hsame T (append I Gamma) ∧
      hsame D (append T S) ∧
        hsame R (append D Q) ∧
          hsame C (append R H) ∧
            PkgSig bundle P pkg

theorem GaugeIntegralCousinRiemannHandoff [AskSetup] [PackageSetup]
    {I Gamma T S D Q R H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaugeIntegralCarrier I Gamma T S D Q R H C P N bundle pkg ->
      Cont I Gamma T ->
        Cont T S D ->
          Cont D Q R ->
            Cont R H C ->
              PkgSig bundle P pkg ->
                GaugeIntegralRoute I Gamma T S D Q R H C P N bundle pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame
  intro carrier intervalGauge cousinRiemann darbouxRegulated realReplay provenance
  exact
    ⟨carrier, intervalGauge, cousinRiemann, darbouxRegulated, realReplay, provenance⟩

end BEDC.Derived.GaugeIntegralUp
