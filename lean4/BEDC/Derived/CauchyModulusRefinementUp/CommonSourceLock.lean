import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_common_source_lock [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n sourceLeft sourceRight : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      hsame m0 m1 →
        Cont m0 u sourceLeft →
          Cont m1 u sourceRight →
            UnaryHistory sourceLeft ∧ UnaryHistory sourceRight ∧
              hsame sourceLeft sourceRight ∧ Cont m0 m1 u ∧ Cont u v t ∧
                PkgSig bundle p pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro carrier sameSources leftRead rightRead
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, _vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have sourceLeftUnary : UnaryHistory sourceLeft :=
    unary_cont_closed m0Unary uUnary leftRead
  have sourceRightUnary : UnaryHistory sourceRight :=
    unary_cont_closed m1Unary uUnary rightRead
  have sameReads : hsame sourceLeft sourceRight :=
    cont_respects_hsame sameSources (hsame_refl u) leftRead rightRead
  exact ⟨sourceLeftUnary, sourceRightUnary, sameReads, m0m1u, uvt, pPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
