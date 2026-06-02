import BEDC.Derived.NormedSpaceUp

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def NormedSpaceCompletionWindowCarrier [AskSetup] [PackageSetup]
    (V R N M Q H T P C metricRead completionRead replayRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  NormedSpaceCarrier V R N M Q H T P C bundle pkg ∧
    Cont V N metricRead ∧ Cont metricRead Q completionRead ∧
      Cont completionRead H replayRead ∧ PkgSig bundle P pkg

end BEDC.Derived.NormedSpaceUp
