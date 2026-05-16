import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
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

theorem RealLimitUniquenessSealCarrier_nonescape [AskSetup] [PackageSetup]
    {l0 l1 q s d r v h c p n routeRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealLimitUniquenessSealCarrier l0 l1 q s d r v h c p n bundle pkg ->
      Cont l0 v routeRead ->
        PkgSig bundle routeRead pkg ->
          UnaryHistory routeRead ∧ PkgSig bundle n pkg ∧ PkgSig bundle routeRead pkg ∧
            (Cont routeRead (BHist.e0 hostTail) l0 -> False) ∧
              (Cont routeRead (BHist.e1 hostTail) l0 -> False) := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier l0VRoute routeReadPkg
  obtain ⟨l0Unary, _l1Unary, _qUnary, _sUnary, _dUnary, _rUnary, vUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _l0l1q, _qsd, _drv, _hcp, nPkg⟩ := carrier
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed l0Unary vUnary l0VRoute
  exact
    ⟨routeUnary, nPkg, routeReadPkg,
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left l0VRoute hostReturn),
      (fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right l0VRoute hostReturn)⟩

end BEDC.Derived.RealLimitUniquenessSealUp
