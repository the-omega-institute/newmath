import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealLimitUniquenessSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealLimitUniquenessSealCarrier [AskSetup] [PackageSetup]
    (l0 l1 q s d r v h c p n : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  UnaryHistory l0 ∧ UnaryHistory l1 ∧ UnaryHistory q ∧ UnaryHistory s ∧
    UnaryHistory d ∧ UnaryHistory r ∧ UnaryHistory v ∧ UnaryHistory h ∧
      UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧ Cont l0 l1 q ∧
        Cont q s d ∧ Cont d r v ∧ Cont h c p ∧ PkgSig bundle n pkg

theorem RealLimitUniquenessSealCarrier_obligation_surface [AskSetup] [PackageSetup]
    {l0 l1 q s d r v h c p n : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealLimitUniquenessSealCarrier l0 l1 q s d r v h c p n bundle pkg ->
      UnaryHistory l0 ∧ UnaryHistory l1 ∧ UnaryHistory q ∧ UnaryHistory s ∧
        UnaryHistory d ∧ UnaryHistory r ∧ UnaryHistory v ∧ UnaryHistory h ∧
          UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧ Cont l0 l1 q ∧
            Cont q s d ∧ Cont d r v ∧ Cont h c p ∧ PkgSig bundle n pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier
  rcases carrier with
    ⟨l0Unary, l1Unary, qUnary, sUnary, dUnary, rUnary, vUnary, hUnary, cUnary,
      pUnary, nUnary, l0l1q, qsd, drv, hcp, nPkg⟩
  exact
    ⟨l0Unary, l1Unary, qUnary, sUnary, dUnary, rUnary, vUnary, hUnary, cUnary,
      pUnary, nUnary, l0l1q, qsd, drv, hcp, nPkg⟩

end BEDC.Derived.RealLimitUniquenessSealUp
