import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_source_window_strict_obstruction [AskSetup]
    [PackageSetup] {m0 m1 u v t w q e h c p n offRouteTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      (Cont m0 (BHist.e0 offRouteTail) u -> False) ∧
        (Cont m0 (BHist.e1 offRouteTail) u -> hsame m1 (BHist.e1 offRouteTail)) ∧
          Cont m0 m1 u ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier
  rcases carrier with
    ⟨_m0Unary, m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, _uvt, _twq, _qeh, pPkg, _hn⟩
  have zeroObstruction : Cont m0 (BHist.e0 offRouteTail) u -> False := by
    intro zeroRoute
    exact unary_history_hsame_zero_absurd m1Unary (cont_left_cancel m0m1u zeroRoute)
  have oneIdentification :
      Cont m0 (BHist.e1 offRouteTail) u -> hsame m1 (BHist.e1 offRouteTail) := by
    intro oneRoute
    exact cont_left_cancel m0m1u oneRoute
  exact ⟨zeroObstruction, oneIdentification, m0m1u, pPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
