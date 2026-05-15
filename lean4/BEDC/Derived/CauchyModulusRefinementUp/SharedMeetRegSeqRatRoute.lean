import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_shared_meet_regseqrat_route
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧ UnaryHistory v ∧
                UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory selected ∧
                  UnaryHistory readback ∧ UnaryHistory sealRead ∧ Cont m0 m1 u ∧
                    Cont u v t ∧ Cont t w selected ∧ Cont selected q readback ∧
                      Cont readback e sealRead ∧ PkgSig bundle p pkg ∧
                        PkgSig bundle sealRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier tWSelected selectedQReadback readbackESealRead sealReadPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESealRead
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, selectedUnary, readbackUnary,
      sealReadUnary, m0m1u, uvt, tWSelected, selectedQReadback, readbackESealRead,
      pPkg, sealReadPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
