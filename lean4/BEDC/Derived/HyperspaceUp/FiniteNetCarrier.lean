import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def HyperspaceFiniteNetCarrier [AskSetup] [PackageSetup]
    (X K0 K1 N0 N1 D0 D1 R Hs C P M : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ∧
    Cont X K0 N0 ∧ Cont K1 N1 D0

end BEDC.Derived.HyperspaceUp
