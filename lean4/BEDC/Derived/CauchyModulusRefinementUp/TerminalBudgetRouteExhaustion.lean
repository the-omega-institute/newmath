import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_terminal_budget_route_exhaustion
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n selected readback sealRead publicRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      Cont t w selected ->
        Cont selected q readback ->
          Cont readback e sealRead ->
            Cont sealRead h publicRead ->
              Cont publicRead c terminal ->
                PkgSig bundle terminal pkg ->
                  UnaryHistory selected ∧ UnaryHistory readback ∧ UnaryHistory sealRead ∧
                    UnaryHistory publicRead ∧ UnaryHistory terminal ∧ Cont m0 m1 u ∧
                      Cont u v t ∧ Cont t w selected ∧ Cont selected q readback ∧
                        Cont readback e sealRead ∧ Cont sealRead h publicRead ∧
                          Cont publicRead c terminal ∧ PkgSig bundle p pkg ∧
                            PkgSig bundle terminal pkg ∧ hsame h n := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory ProbeBundle
  intro carrier tWSelected selectedQReadback readbackESeal sealHPublic publicCTerminal
    terminalPkg
  rcases carrier with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
      cUnary, _pUnary, _nUnary, m0m1u, uvt, _twq, _qeh, pPkg, hn⟩
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary tWSelected
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary selectedQReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary readbackESeal
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary hUnary sealHPublic
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed publicReadUnary cUnary publicCTerminal
  exact
    ⟨selectedUnary, readbackUnary, sealReadUnary, publicReadUnary, terminalUnary, m0m1u,
      uvt, tWSelected, selectedQReadback, readbackESeal, sealHPublic, publicCTerminal,
      pPkg, terminalPkg, hn⟩

end BEDC.Derived.CauchyModulusRefinementUp
