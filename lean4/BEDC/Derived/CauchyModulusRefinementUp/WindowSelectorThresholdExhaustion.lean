import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementPacket_window_selector_threshold_exhaustion
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory u ∧ UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory q ∧
                  UnaryHistory selected ∧ UnaryHistory readback ∧ UnaryHistory sealRead ∧
                    UnaryHistory publicRead ∧ Cont u v t ∧ Cont t w selected ∧
                      Cont selected q readback ∧ Cont readback e sealRead ∧
                        Cont sealRead h publicRead ∧ PkgSig bundle p pkg ∧
                          PkgSig bundle publicRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory ProbeBundle
  intro carrier tWSelected selectedQReadback readbackESeal sealHPublic publicPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESeal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary hUnary sealHPublic
  exact
    ⟨uUnary, tUnary, wUnary, qUnary, selectedUnary, readbackUnary, sealReadUnary,
      publicReadUnary, uvt, tWSelected, selectedQReadback, readbackESeal, sealHPublic, pPkg,
      publicPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
