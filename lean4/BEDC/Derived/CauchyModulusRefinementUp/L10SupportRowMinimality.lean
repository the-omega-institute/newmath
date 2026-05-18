import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementL10SupportRowMinimality [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n supportRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont h c supportRead ->
        Cont supportRead n endpoint ->
          PkgSig bundle endpoint pkg ->
            UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
              UnaryHistory supportRead ∧ UnaryHistory endpoint ∧ Cont h c supportRead ∧
                Cont supportRead n endpoint ∧ hsame h n ∧ PkgSig bundle p pkg ∧
                  PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier supportRoute endpointRoute endpointPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      hUnary, cUnary, pUnary, nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, hn⟩
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed hUnary cUnary supportRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed supportReadUnary nUnary endpointRoute
  exact
    ⟨hUnary, cUnary, pUnary, nUnary, supportReadUnary, endpointUnary, supportRoute,
      endpointRoute, hn, pPkg, endpointPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
