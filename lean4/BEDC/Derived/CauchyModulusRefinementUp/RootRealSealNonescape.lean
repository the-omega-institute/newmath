import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_root_real_seal_nonescape [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n rootRead selectorRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont m0 u rootRead →
        Cont rootRead t selectorRead →
          Cont selectorRead e realRead →
            PkgSig bundle realRead pkg →
              UnaryHistory rootRead ∧ UnaryHistory selectorRead ∧ UnaryHistory realRead ∧
                Cont m0 u rootRead ∧ Cont rootRead t selectorRead ∧
                  Cont selectorRead e realRead ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle realRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier rootRoute selectorRoute realRoute realPkg
  rcases carrier with
    ⟨m0Unary, _m1Unary, uUnary, _vUnary, tUnary, _wUnary, _qUnary, eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, hn⟩
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed m0Unary uUnary rootRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed rootUnary tUnary selectorRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed selectorUnary eUnary realRoute
  exact ⟨rootUnary, selectorUnary, realUnary, rootRoute, selectorRoute, realRoute, pPkg, realPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
