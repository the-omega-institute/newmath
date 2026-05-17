import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_l10_consumer_spine_comparison [AskSetup]
    [PackageSetup]
    {m0 m1 u v t w q e h c p n diagonalRead l10Read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w diagonalRead ->
        Cont diagonalRead q l10Read ->
          PkgSig bundle l10Read pkg ->
            UnaryHistory diagonalRead ∧ UnaryHistory l10Read ∧ Cont m0 m1 u ∧
              Cont u v t ∧ Cont t w diagonalRead ∧ Cont diagonalRead q l10Read ∧
                PkgSig bundle p pkg ∧ PkgSig bundle l10Read pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier tWDiagonal diagonalQL10 l10Pkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed tUnary wUnary tWDiagonal
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed diagonalUnary qUnary diagonalQL10
  exact
    ⟨diagonalUnary, l10Unary, m0m1u, uvt, tWDiagonal, diagonalQL10, pPkg, l10Pkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
