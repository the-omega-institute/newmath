import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_selector_nonempty_route [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h publicRead ->
              PkgSig bundle publicRead pkg ->
                UnaryHistory t ∧ UnaryHistory w ∧ UnaryHistory selected ∧
                  UnaryHistory q ∧ UnaryHistory readback ∧ UnaryHistory e ∧
                    UnaryHistory sealRead ∧ UnaryHistory h ∧ UnaryHistory publicRead ∧
                      Cont t w selected ∧ Cont selected q readback ∧
                        Cont readback e sealRead ∧ Cont sealRead h publicRead ∧
                          PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg ∧
                            hsame h n := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro carrier twSelected selectedQReadback readbackESeal sealHPublic publicPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary twSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESeal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary hUnary sealHPublic
  exact
    ⟨tUnary, wUnary, selectedUnary, qUnary, readbackUnary, eUnary, sealUnary, hUnary,
      publicUnary, twSelected, selectedQReadback, readbackESeal, sealHPublic, pPkg,
      publicPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
