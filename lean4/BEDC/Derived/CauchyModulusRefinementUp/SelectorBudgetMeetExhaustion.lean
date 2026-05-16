import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_selector_budget_meet_exhaustion
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont q e realRead ->
        PkgSig bundle realRead pkg ->
          UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
            UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
              UnaryHistory realRead ∧ Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧
                Cont q e realRead ∧ PkgSig bundle p pkg ∧
                  PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier qERealRead realReadPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, _qeh, pPkg, _hn⟩
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed qUnary eUnary qERealRead
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary,
      realReadUnary, m0m1u, uvt, twq, qERealRead, pPkg, realReadPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
