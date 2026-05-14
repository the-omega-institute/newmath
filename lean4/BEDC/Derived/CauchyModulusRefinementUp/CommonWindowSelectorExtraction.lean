import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCommonWindowSelectorExtraction [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback h publicRead ->
            PkgSig bundle publicRead pkg ->
              UnaryHistory selected ∧ UnaryHistory readback ∧ UnaryHistory publicRead ∧
                Cont m0 m1 u ∧ Cont u v t ∧ Cont t w selected ∧
                  Cont selected q readback ∧ Cont readback h publicRead ∧
                    PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle hsame UnaryHistory
  intro carrier tWSelected selectedQReadback readbackHPublicRead publicReadPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, _eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed readbackUnary hUnary readbackHPublicRead
  exact
    ⟨selectedUnary, readbackUnary, publicReadUnary, m0m1u, uvt, tWSelected,
      selectedQReadback, readbackHPublicRead, pPkg, publicReadPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
