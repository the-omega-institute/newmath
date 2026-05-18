import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ContinuationMonadKernelScopeRow [AskSetup] [PackageSetup]
    (A B C f g u H K L N scopeRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  ContinuationMonadCarrier A B C f g u H K L N ∧ Cont L N scopeRead ∧
    PkgSig bundle scopeRead pkg ∧ UnaryHistory scopeRead

end BEDC.Derived.ContinuationMonadUp
