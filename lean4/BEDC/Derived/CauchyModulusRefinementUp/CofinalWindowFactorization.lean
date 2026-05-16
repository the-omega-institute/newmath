import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_cofinal_window_factorization
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n cofinalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont t w cofinalRead →
        PkgSig bundle cofinalRead pkg →
          UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
            UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧
              UnaryHistory cofinalRead ∧ Cont m0 m1 u ∧ Cont u v t ∧
                Cont t w q ∧ Cont t w cofinalRead ∧ hsame q cofinalRead ∧
                  PkgSig bundle p pkg ∧ PkgSig bundle cofinalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame ProbeBundle Pkg
  intro carrier cofinalRoute cofinalPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, _eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, _qeh, pPkg, _hn⟩
  have cofinalUnary : UnaryHistory cofinalRead :=
    unary_cont_closed tUnary wUnary cofinalRoute
  have sameCofinal : hsame q cofinalRead :=
    cont_deterministic twq cofinalRoute
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, cofinalUnary,
      m0m1u, uvt, twq, cofinalRoute, sameCofinal, pPkg, cofinalPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
