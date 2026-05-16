import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyModulusRefinementSharedTailSelectorWindowDeterminacy
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n tailBudget wPrime qPrime ePrime hPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      hsame w wPrime ->
        hsame e ePrime ->
          Cont t wPrime qPrime ->
            Cont qPrime ePrime hPrime ->
              PkgSig bundle tailBudget pkg ->
                hsame q qPrime /\ hsame h hPrime /\ PkgSig bundle tailBudget pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  intro carrier sameWindow sameSeal transportedWindow transportedSeal tailBudgetPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, carrierWindow,
      carrierSeal, _pPkg, _hn⟩
  have sameQ : hsame q qPrime :=
    cont_respects_hsame (hsame_refl t) sameWindow carrierWindow transportedWindow
  have sameH : hsame h hPrime :=
    cont_respects_hsame sameQ sameSeal carrierSeal transportedSeal
  exact ⟨sameQ, sameH, tailBudgetPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
