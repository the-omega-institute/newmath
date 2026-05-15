import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_diagonal_budget_cofinality_route [AskSetup]
    [PackageSetup] {m0 m1 u v t w q e h c p n diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont q e diagonalRead ->
        PkgSig bundle diagonalRead pkg ->
          UnaryHistory diagonalRead ∧ Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧
            Cont q e diagonalRead ∧ PkgSig bundle p pkg ∧
              PkgSig bundle diagonalRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame ProbeBundle Pkg
  intro carrier diagonalRoute diagonalPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, qUnary, eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, _qeh, pPkg, hn⟩
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed qUnary eUnary diagonalRoute
  exact ⟨diagonalUnary, m0m1u, uvt, twq, diagonalRoute, pPkg, diagonalPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
