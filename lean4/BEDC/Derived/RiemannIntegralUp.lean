import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.RiemannIntegralUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive RiemannIntegralUp : Type where
  | mk (M T F S D G R H C P N : BHist) : RiemannIntegralUp
  deriving DecidableEq

def RiemannIntegralCarrier [AskSetup] [PackageSetup]
    (M T F S D G R H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory F ∧ UnaryHistory S ∧
    UnaryHistory D ∧ UnaryHistory G ∧ UnaryHistory R ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory N ∧ Cont M T F ∧ Cont F S D ∧
        Cont D G R ∧ PkgSig bundle P pkg

end BEDC.Derived.RiemannIntegralUp
