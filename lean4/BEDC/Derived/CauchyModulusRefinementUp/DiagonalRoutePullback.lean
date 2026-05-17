import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_diagonal_route_pullback [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n diagonalRoute endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont t w diagonalRoute →
        Cont diagonalRoute q endpoint →
          PkgSig bundle endpoint pkg →
            UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧
              UnaryHistory diagonalRoute ∧ UnaryHistory endpoint ∧
                Cont t w diagonalRoute ∧ Cont diagonalRoute q endpoint ∧
                  PkgSig bundle p pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro carrier tWDiagonal diagonalQEndpoint endpointPkg
  obtain ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, _eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg,
    _hn⟩ := carrier
  have diagonalUnary : UnaryHistory diagonalRoute :=
    unary_cont_closed tUnary wUnary tWDiagonal
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed diagonalUnary qUnary diagonalQEndpoint
  exact
    ⟨tUnary, wUnary, qUnary, diagonalUnary, endpointUnary, tWDiagonal,
      diagonalQEndpoint, pPkg, endpointPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
