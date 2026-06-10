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

def CalculusRootPublicPackage [AskSetup] [PackageSetup]
    (E R D L J H C P N rootC rootD rootI rootL rootR rootQ rootY rootH rootT rootP
      rootN : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  UnaryHistory E ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory L ∧
    UnaryHistory J ∧ Cont E R C ∧ Cont rootL rootC rootT ∧ hsame H C ∧
      hsame rootH rootT ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
        PkgSig bundle rootP pkg ∧ PkgSig bundle rootN pkg

end BEDC.Derived.CalculusUp
