import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_shared_tail_handoff [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t q tailRead ->
        PkgSig bundle tailRead pkg ->
          UnaryHistory tailRead ∧ Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧
            Cont t q tailRead ∧ Cont q e h ∧ PkgSig bundle p pkg ∧
              PkgSig bundle tailRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro carrier tailRoute tailPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, _wUnary, qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed tUnary qUnary tailRoute
  exact ⟨tailUnary, m0m1u, uvt, twq, tailRoute, qeh, pPkg, tailPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
