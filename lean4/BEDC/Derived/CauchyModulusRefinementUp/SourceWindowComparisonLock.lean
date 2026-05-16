import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_source_window_comparison_lock
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n t2 w2 q2 e2 h2 c2 p2 n2 sourceFront
      sourceFront2 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      CauchyModulusRefinementCarrier m0 m1 u v t2 w2 q2 e2 h2 c2 p2 n2 bundle pkg ->
        Cont m0 u sourceFront ->
          Cont m0 u sourceFront2 ->
            UnaryHistory sourceFront ∧ UnaryHistory sourceFront2 ∧
              hsame sourceFront sourceFront2 ∧ Cont m0 m1 u ∧ Cont m0 u sourceFront ∧
                Cont m0 u sourceFront2 := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro carrier carrier2 m0USourceFront m0USourceFront2
  rcases carrier with
    ⟨m0Unary, _m1Unary, uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, _uvt, _twq, _qeh, _pPkg, _hn⟩
  rcases carrier2 with
    ⟨_m0Unary2, _m1Unary2, _uUnary2, _vUnary2, _tUnary2, _wUnary2, _qUnary2,
      _eUnary2, _hUnary2, _cUnary2, _pUnary2, _nUnary2, _m0m1u2, _uvt2, _twq2,
      _qeh2, _pPkg2, _hn2⟩
  have sourceFrontUnary : UnaryHistory sourceFront :=
    unary_cont_closed m0Unary uUnary m0USourceFront
  have sourceFront2Unary : UnaryHistory sourceFront2 :=
    unary_cont_closed m0Unary uUnary m0USourceFront2
  have sameSourceFront : hsame sourceFront sourceFront2 :=
    cont_respects_hsame (hsame_refl m0) (hsame_refl u) m0USourceFront m0USourceFront2
  exact
    ⟨sourceFrontUnary, sourceFront2Unary, sameSourceFront, m0m1u, m0USourceFront,
      m0USourceFront2⟩

end BEDC.Derived.CauchyModulusRefinementUp
