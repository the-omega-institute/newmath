import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyModulusRefinementCarrier_shared_tail_selector_determinacy
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n tPrime wPrime qPrime ePrime hPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      hsame t tPrime ->
        hsame w wPrime ->
          hsame e ePrime ->
            Cont tPrime wPrime qPrime ->
              Cont qPrime ePrime hPrime ->
                hsame q qPrime /\ hsame h hPrime /\ PkgSig bundle p pkg /\ hsame h n := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig
  intro carrier sameSelector sameWindow sameSeal transportedWindow transportedSeal
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, carrierWindow,
      carrierSeal, pPkg, hn⟩
  have sameQ : hsame q qPrime :=
    cont_respects_hsame sameSelector sameWindow carrierWindow transportedWindow
  have sameH : hsame h hPrime :=
    cont_respects_hsame sameQ sameSeal carrierSeal transportedSeal
  exact ⟨sameQ, sameH, pPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
