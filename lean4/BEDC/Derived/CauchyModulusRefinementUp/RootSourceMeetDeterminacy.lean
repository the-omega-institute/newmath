import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_root_source_meet_determinacy
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n front selected : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont u v front ->
        Cont front w selected ->
          PkgSig bundle selected pkg ->
            UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
              UnaryHistory front ∧ UnaryHistory selected ∧ hsame t front ∧
                Cont m0 m1 u ∧ Cont u v front ∧ Cont front w selected ∧
                  PkgSig bundle p pkg ∧ PkgSig bundle selected pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier uvFront frontWSelected selectedPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, _tUnary, wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, _hn⟩
  have frontUnary : UnaryHistory front :=
    unary_cont_closed uUnary vUnary uvFront
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed frontUnary wUnary frontWSelected
  have sameFront : hsame t front :=
    cont_respects_hsame (hsame_refl u) (hsame_refl v) uvt uvFront
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, frontUnary, selectedUnary, sameFront,
      m0m1u, uvFront, frontWSelected, pPkg, selectedPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
