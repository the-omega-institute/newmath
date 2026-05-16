import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_regseq_real_selector_exactness
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont q e tailRead ->
              PkgSig bundle sealRead pkg ->
                PkgSig bundle tailRead pkg ->
                  UnaryHistory selected ∧ UnaryHistory readback ∧ UnaryHistory sealRead ∧
                    UnaryHistory tailRead ∧ Cont t w selected ∧
                      Cont selected q readback ∧ Cont readback e sealRead ∧
                        Cont q e tailRead ∧ PkgSig bundle sealRead pkg ∧
                          PkgSig bundle tailRead pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier selectedRoute readbackRoute sealRoute tailRoute sealPkg tailPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary,
      _hUnary, _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, _pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed qUnary eUnary tailRoute
  exact
    ⟨selectedUnary, readbackUnary, sealUnary, tailUnary, selectedRoute, readbackRoute,
      sealRoute, tailRoute, sealPkg, tailPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
