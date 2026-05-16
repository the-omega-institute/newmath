import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_real_limit_uniqueness_handoff
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n limitRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont q e sealRead ->
        Cont sealRead h limitRead ->
          PkgSig bundle limitRead pkg ->
            UnaryHistory sealRead ∧ UnaryHistory limitRead ∧ Cont m0 m1 u ∧
              Cont u v t ∧ Cont t w q ∧ Cont q e sealRead ∧
                Cont sealRead h limitRead ∧ PkgSig bundle p pkg ∧
                  PkgSig bundle limitRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier sealRoute limitRoute limitPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, _qeh, pPkg, hn⟩
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed qUnary eUnary sealRoute
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed sealUnary hUnary limitRoute
  exact
    ⟨sealUnary, limitUnary, m0m1u, uvt, twq, sealRoute, limitRoute, pPkg,
      limitPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
