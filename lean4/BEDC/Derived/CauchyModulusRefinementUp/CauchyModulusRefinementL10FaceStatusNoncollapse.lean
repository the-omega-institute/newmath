import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_l10_face_status_noncollapse [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n aggregateTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      (Cont q (BHist.e0 aggregateTail) h -> False) ∧
        (Cont q (BHist.e1 aggregateTail) h -> hsame e (BHist.e1 aggregateTail)) ∧
          Cont q e h ∧ PkgSig bundle p pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, _tUnary, _wUnary, _qUnary, eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, qeh, pPkg, hn⟩
  have zeroObstruction : Cont q (BHist.e0 aggregateTail) h -> False := by
    intro zeroRoute
    exact unary_history_hsame_zero_absurd eUnary (cont_left_cancel qeh zeroRoute)
  have oneIdentification :
      Cont q (BHist.e1 aggregateTail) h -> hsame e (BHist.e1 aggregateTail) := by
    intro oneRoute
    exact cont_left_cancel qeh oneRoute
  exact ⟨zeroObstruction, oneIdentification, qeh, pPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
