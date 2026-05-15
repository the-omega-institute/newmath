import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyModulusRefinementCarrier_tail_budget_seal_uniqueness [AskSetup]
    [PackageSetup]
    {m0 m1 u v t w q e h c p n tPrime wPrime qPrime ePrime hPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      hsame t tPrime ->
        hsame w wPrime ->
          hsame e ePrime ->
            Cont tPrime wPrime qPrime ->
              Cont qPrime ePrime hPrime ->
                hsame q qPrime ∧ hsame h hPrime := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier sameT sameW sameE transportedBudget transportedSeal
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, twq, qeh, _pPkg, _hn⟩
  have sameQ : hsame q qPrime :=
    cont_respects_hsame sameT sameW twq transportedBudget
  have sameH : hsame h hPrime :=
    cont_respects_hsame sameQ sameE qeh transportedSeal
  exact ⟨sameQ, sameH⟩

end BEDC.Derived.CauchyModulusRefinementUp
