import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_shared_threshold_transport [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n threshold witness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont u v threshold →
        Cont threshold h witness →
          PkgSig bundle witness pkg →
            UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
              UnaryHistory threshold ∧ UnaryHistory witness ∧ hsame t threshold ∧
                hsame h n ∧ Cont m0 m1 u ∧ Cont u v threshold ∧
                  Cont threshold h witness ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle witness pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg
  intro carrier thresholdRoute witnessRoute witnessPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed uUnary vUnary thresholdRoute
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed thresholdUnary hUnary witnessRoute
  have sameThreshold : hsame t threshold :=
    cont_respects_hsame (hsame_refl u) (hsame_refl v) uvt thresholdRoute
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, thresholdUnary, witnessUnary, sameThreshold,
      hn, m0m1u, thresholdRoute, witnessRoute, pPkg, witnessPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
