import BEDC.Derived.CauchyModulusRefinementUp
import BEDC.Derived.FiniteObservationBudgetSelectorUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.FiniteObservationBudgetSelectorUp

theorem CauchyModulusRefinementCarrier_finite_observation_budget_pullback
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n b s fw d r fe fh fc fp fn selectorRead realRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      FiniteObservationBudgetSelectorCarrier b s fw d r fe fh fc fp fn ->
        hsame w fw ->
          hsame q d ->
            hsame t r ->
              hsame e fe ->
                Cont r fe selectorRead ->
                  Cont q e realRead ->
                    PkgSig bundle selectorRead pkg ->
                      PkgSig bundle realRead pkg ->
                        UnaryHistory m0 ∧ UnaryHistory m1 ∧ UnaryHistory u ∧
                          UnaryHistory v ∧ UnaryHistory t ∧ UnaryHistory w ∧
                            UnaryHistory q ∧ UnaryHistory e ∧ UnaryHistory selectorRead ∧
                              UnaryHistory realRead ∧
                                FiniteObservationBudgetSelectorCarrier b s fw d r fe fh fc
                                  fp fn ∧
                                  Cont m0 m1 u ∧ Cont u v t ∧ Cont t w q ∧
                                    Cont q e realRead ∧ Cont r fe selectorRead ∧
                                      hsame w fw ∧ hsame q d ∧ hsame t r ∧ hsame e fe ∧
                                        PkgSig bundle p pkg ∧
                                          PkgSig bundle selectorRead pkg ∧
                                            PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro refinement selector sameWindow sameDyadic sameTail sameSeal selectorRoute realRoute
    selectorPkg realPkg
  have selectorFull :
      FiniteObservationBudgetSelectorCarrier b s fw d r fe fh fc fp fn :=
    selector
  obtain ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, m0m1u, uvt, twq, _qeh, pPkg, _hn⟩ :=
    refinement
  obtain ⟨bUnary, sUnary, dUnary, feUnary, _fhUnary, bSfw, fwDr, _rFefc, _fnfe⟩ :=
    selector
  have fwUnary : UnaryHistory fw :=
    unary_cont_closed bUnary sUnary bSfw
  have rUnary : UnaryHistory r :=
    unary_cont_closed fwUnary dUnary fwDr
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed rUnary feUnary selectorRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed qUnary eUnary realRoute
  exact
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary,
      selectorReadUnary, realReadUnary, selectorFull, m0m1u, uvt, twq, realRoute,
      selectorRoute, sameWindow, sameDyadic, sameTail, sameSeal, pPkg, selectorPkg, realPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
