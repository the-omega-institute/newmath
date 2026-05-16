import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_source_meet_exactness [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n sourceMeet refinementRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont m0 m1 sourceMeet →
        hsame sourceMeet u →
          Cont sourceMeet v refinementRead →
            PkgSig bundle refinementRead pkg →
              UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
                UnaryHistory sourceMeet ∧ UnaryHistory refinementRead ∧
                  Cont m0 m1 sourceMeet ∧ Cont sourceMeet v refinementRead ∧
                    Cont m0 m1 u ∧ Cont u v t ∧ PkgSig bundle p pkg ∧
                      PkgSig bundle refinementRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sourceMeetRoute _sourceMeetSame refinementRoute refinementPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, _tUnary, _wUnary, _qUnary, _eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, _hn⟩
  have sourceMeetUnary : UnaryHistory sourceMeet :=
    unary_cont_closed m0Unary m1Unary sourceMeetRoute
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed sourceMeetUnary vUnary refinementRoute
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, sourceMeetUnary, refinementReadUnary,
      sourceMeetRoute, refinementRoute, m0m1u, uvt, pPkg, refinementPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
