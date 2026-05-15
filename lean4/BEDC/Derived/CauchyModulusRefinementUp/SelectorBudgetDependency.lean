import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_selector_budget_dependency [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selectedRead toleranceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont v t selectedRead →
        Cont selectedRead w toleranceRead →
          UnaryHistory v ∧ UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧
            UnaryHistory selectedRead ∧ UnaryHistory toleranceRead ∧ Cont u v t ∧
              Cont t w q ∧ Cont v t selectedRead ∧
                Cont selectedRead w toleranceRead ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier selectorRoute toleranceRoute
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, vUnary, tUnary, wUnary, qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, uvt, twq, _qeh, pPkg, _hn⟩
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed vUnary tUnary selectorRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed selectedUnary wUnary toleranceRoute
  exact
    ⟨vUnary, tUnary, wUnary, qUnary, selectedUnary, toleranceUnary, uvt, twq,
      selectorRoute, toleranceRoute, pPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
