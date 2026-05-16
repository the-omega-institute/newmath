import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_root_budget_consumer_exhaustion
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧ UnaryHistory e ∧
                UnaryHistory selected ∧ UnaryHistory readback ∧ UnaryHistory sealRead ∧
                  Cont t w selected ∧ Cont selected q readback ∧ Cont readback e sealRead ∧
                    PkgSig bundle p pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro carrier tWSelected selectedQReadback readbackESeal sealPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, _hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESeal
  exact
    ⟨tUnary, wUnary, qUnary, eUnary, selectedUnary, readbackUnary, sealReadUnary,
      tWSelected, selectedQReadback, readbackESeal, pPkg, sealPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
