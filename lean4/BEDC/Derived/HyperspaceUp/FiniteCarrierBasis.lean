import BEDC.Derived.HyperspaceUp.TasteGate

namespace BEDC.Derived.HyperspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def HyperspaceFiniteCarrierBasis [AskSetup] [PackageSetup]
    (X K0 K1 N0 N1 D0 D1 R Hs C P M finiteHit finiteReplay : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg ∧
    Cont K0 K1 finiteHit ∧ Cont Hs C finiteReplay ∧ PkgSig bundle P pkg

end BEDC.Derived.HyperspaceUp
