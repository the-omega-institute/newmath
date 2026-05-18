import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyModulusRefinementL10FaceStatusPullbackRecord [AskSetup] [PackageSetup]
    (m0 m1 u v t w q e h c p n face : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
    Cont h c face ∧ UnaryHistory face ∧ PkgSig bundle face pkg

end BEDC.Derived.CauchyModulusRefinementUp
