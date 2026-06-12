import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CalculusRootObligationSurface [AskSetup] [PackageSetup]
    (C D I L R Q Y H T P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory C ∧ UnaryHistory D ∧ UnaryHistory I ∧ UnaryHistory L ∧
    UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory Y ∧ UnaryHistory H ∧
      UnaryHistory T ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont C D I ∧
        Cont L Q Y ∧ Cont Y R T ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

end BEDC.Derived.CalculusUp
