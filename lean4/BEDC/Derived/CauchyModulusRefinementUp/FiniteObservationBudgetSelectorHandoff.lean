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

theorem CauchyModulusRefinementCarrier_finite_observation_budget_selector_handoff
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n b s fw d r fe fh fc fp fn selected selectorSeal
      l10Seal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      FiniteObservationBudgetSelectorCarrier b s fw d r fe fh fc fp fn ->
        Cont t w selected ->
          hsame selected fw ->
            hsame q d ->
              hsame e fe ->
                Cont r fe selectorSeal ->
                  Cont q e l10Seal ->
                    PkgSig bundle selectorSeal pkg ->
                      PkgSig bundle l10Seal pkg ->
                        UnaryHistory selected ∧ UnaryHistory selectorSeal ∧
                          UnaryHistory l10Seal ∧ Cont t w selected ∧
                            Cont r fe selectorSeal ∧ Cont q e l10Seal ∧
                              hsame selected fw ∧ hsame q d ∧ hsame e fe ∧
                                PkgSig bundle selectorSeal pkg ∧
                                  PkgSig bundle l10Seal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro refinement selector selectedRoute sameSelected sameTolerance sameSeal selectorSealRoute
    l10SealRoute selectorSealPkg l10SealPkg
  rcases refinement with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, _pPkg, _hn⟩
  rcases selector with
    ⟨bUnary, sUnary, dUnary, feUnary, bSfw, fwDr, _rFefc, _fnfe⟩
  have fwUnary : UnaryHistory fw :=
    unary_cont_closed bUnary sUnary bSfw
  have rUnary : UnaryHistory r :=
    unary_cont_closed fwUnary dUnary fwDr
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have selectorSealUnary : UnaryHistory selectorSeal :=
    unary_cont_closed rUnary feUnary selectorSealRoute
  have l10SealUnary : UnaryHistory l10Seal :=
    unary_cont_closed qUnary eUnary l10SealRoute
  exact
    ⟨selectedUnary, selectorSealUnary, l10SealUnary, selectedRoute, selectorSealRoute,
      l10SealRoute, sameSelected, sameTolerance, sameSeal, selectorSealPkg, l10SealPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
