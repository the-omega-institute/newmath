import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_l10_handoff_sufficiency [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont w q handoff ->
        PkgSig bundle handoff pkg ->
          UnaryHistory u ∧ UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧
            UnaryHistory e ∧ UnaryHistory handoff ∧ Cont u v t ∧ Cont t w q ∧
              Cont w q handoff ∧ Cont q e h ∧ PkgSig bundle p pkg ∧
                PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier windowReadbackHandoff handoffPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, uvt, twq, qeh, pPkg, _hn⟩
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed wUnary qUnary windowReadbackHandoff
  exact
    ⟨uUnary, tUnary, wUnary, qUnary, eUnary, handoffUnary, uvt, twq,
      windowReadbackHandoff, qeh, pPkg, handoffPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
