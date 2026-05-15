import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_cauchycriterion_selector_cofinality
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selectorRead criterionRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont v t selectorRead ->
        Cont selectorRead q criterionRead ->
          Cont criterionRead e sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory selectorRead ∧ UnaryHistory criterionRead ∧
                UnaryHistory sealRead ∧ Cont m0 m1 u ∧ Cont u v t ∧
                  Cont v t selectorRead ∧ Cont selectorRead q criterionRead ∧
                    Cont criterionRead e sealRead ∧ PkgSig bundle p pkg ∧
                      PkgSig bundle sealRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier vTSelector selectorQCriterion criterionESeal sealPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, vUnary, tUnary, _wUnary, qUnary, eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed vUnary tUnary vTSelector
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed selectorUnary qUnary selectorQCriterion
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed criterionUnary eUnary criterionESeal
  exact
    ⟨selectorUnary, criterionUnary, sealUnary, m0m1u, uvt, vTSelector,
      selectorQCriterion, criterionESeal, pPkg, sealPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
