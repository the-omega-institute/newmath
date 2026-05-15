import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementRootWindowSelectorTotality [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont t w selected →
        Cont selected q readback →
          PkgSig bundle readback pkg →
            UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
              UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory selected ∧
                UnaryHistory readback ∧ Cont m0 m1 u ∧ Cont u v t ∧
                  Cont t w selected ∧ Cont selected q readback ∧ PkgSig bundle p pkg ∧
                    PkgSig bundle readback pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame
  intro carrier tWSelected selectedQReadback readbackPkg
  obtain ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, _eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩ :=
    carrier
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, selectedUnary,
      readbackUnary, m0m1u, uvt, tWSelected, selectedQReadback, pPkg, readbackPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
