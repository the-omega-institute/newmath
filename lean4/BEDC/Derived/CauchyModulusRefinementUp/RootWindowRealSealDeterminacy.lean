import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem CauchyModulusRefinementCarrier_root_window_real_seal_determinacy
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n ePrime hPrime sealRead sealReadPrime
      publicRead publicReadPrime : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      hsame e ePrime ->
        Cont q e sealRead ->
          Cont q ePrime sealReadPrime ->
            Cont q ePrime hPrime ->
              Cont sealRead h publicRead ->
                Cont sealReadPrime hPrime publicReadPrime ->
                  hsame sealRead sealReadPrime ∧ hsame h hPrime ∧
                    hsame publicRead publicReadPrime := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier sameSeal carrierSeal alternateSeal alternateCarrierSeal publicRoute
    alternatePublicRoute
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, qeh, _pPkg, _hn⟩
  have sameSealRead : hsame sealRead sealReadPrime :=
    cont_respects_hsame (hsame_refl q) sameSeal carrierSeal alternateSeal
  have sameH : hsame h hPrime :=
    cont_respects_hsame (hsame_refl q) sameSeal qeh alternateCarrierSeal
  have samePublicRead : hsame publicRead publicReadPrime :=
    cont_respects_hsame sameSealRead sameH publicRoute alternatePublicRoute
  exact ⟨sameSealRead, sameH, samePublicRead⟩

end BEDC.Derived.CauchyModulusRefinementUp
