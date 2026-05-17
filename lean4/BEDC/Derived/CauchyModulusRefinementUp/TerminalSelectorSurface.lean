import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyModulusRefinementTerminalSelectorSurface [AskSetup] [PackageSetup]
    (m0 m1 u v t w q e h c p n selected readback sealRead terminal : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame
  CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
    Cont t w selected ∧
      Cont selected q readback ∧
        Cont readback e sealRead ∧
          Cont sealRead h terminal ∧ PkgSig bundle terminal pkg ∧ hsame h n

theorem CauchyModulusRefinementTerminalSelectorSurface_certificate [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementTerminalSelectorSurface m0 m1 u v t w q e h c p n selected
        readback sealRead terminal bundle pkg →
      UnaryHistory selected ∧ UnaryHistory readback ∧ UnaryHistory sealRead ∧
        UnaryHistory terminal ∧ Cont t w selected ∧ Cont selected q readback ∧
          Cont readback e sealRead ∧ Cont sealRead h terminal ∧
            PkgSig bundle terminal pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory hsame
  intro surface
  rcases surface with
    ⟨carrier, selectedRoute, readbackRoute, sealRoute, terminalRoute, terminalPkg, hn⟩
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, _pPkg, _carrierHn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealUnary hUnary terminalRoute
  exact
    ⟨selectedUnary, readbackUnary, sealUnary, terminalUnary, selectedRoute, readbackRoute,
      sealRoute, terminalRoute, terminalPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
