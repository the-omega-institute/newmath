import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementSharedBudgetPullback [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n shared pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont u t shared ->
        Cont shared w pullback ->
          PkgSig bundle pullback pkg ->
            UnaryHistory u ∧ UnaryHistory t ∧ UnaryHistory shared ∧ UnaryHistory w ∧
              UnaryHistory pullback ∧ Cont u t shared ∧ Cont shared w pullback ∧
                PkgSig bundle p pkg ∧ PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier sharedRoute pullbackRoute pullbackPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, uUnary, _vUnary, tUnary, wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, _hn⟩
  have sharedUnary : UnaryHistory shared :=
    unary_cont_closed uUnary tUnary sharedRoute
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed sharedUnary wUnary pullbackRoute
  exact
    ⟨uUnary, tUnary, sharedUnary, wUnary, pullbackUnary, sharedRoute, pullbackRoute,
      pPkg, pullbackPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
