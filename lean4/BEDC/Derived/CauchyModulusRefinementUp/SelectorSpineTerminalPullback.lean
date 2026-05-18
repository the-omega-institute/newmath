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

theorem CauchyModulusRefinementCarrier_selector_spine_terminal_pullback
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n b s fw d r fe fh fc fp fn selected selectorSeal
      l10Seal terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ->
      FiniteObservationBudgetSelectorCarrier b s fw d r fe fh fc fp fn ->
        Cont t w selected ->
          hsame selected fw ->
            hsame q d ->
              hsame e fe ->
                Cont r fe selectorSeal ->
                  Cont q e l10Seal ->
                    Cont selectorSeal l10Seal terminal ->
                      PkgSig bundle selectorSeal pkg ->
                        PkgSig bundle l10Seal pkg ->
                          PkgSig bundle terminal pkg ->
                            UnaryHistory selected ∧ UnaryHistory selectorSeal ∧
                              UnaryHistory l10Seal ∧ UnaryHistory terminal ∧
                                Cont t w selected ∧ Cont r fe selectorSeal ∧
                                  Cont q e l10Seal ∧ Cont selectorSeal l10Seal terminal ∧
                                    hsame selected fw ∧ hsame q d ∧ hsame e fe ∧
                                      PkgSig bundle selectorSeal pkg ∧
                                        PkgSig bundle l10Seal pkg ∧
                                          PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro refinement selector selectedRoute sameSelected sameQ sameE selectorSealRoute
    l10SealRoute terminalRoute selectorSealPkg l10SealPkg terminalPkg
  rcases refinement with
    ⟨_m0Unary, _m1Unary, _uUnary, _vUnary, tUnary, wUnary, qUnary, eUnary, _hUnary,
      _cUnary, _pUnary, _nUnary, _m0m1u, _uvt, _twq, _qeh, _pPkg, _hn⟩
  rcases selector with
    ⟨bUnary, sUnary, dUnary, feUnary, _fhUnary, bSfw, fwDr, _rFefc, _fnfe⟩
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
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed selectorSealUnary l10SealUnary terminalRoute
  exact
    ⟨selectedUnary, selectorSealUnary, l10SealUnary, terminalUnary, selectedRoute,
      selectorSealRoute, l10SealRoute, terminalRoute, sameSelected, sameQ, sameE,
      selectorSealPkg, l10SealPkg, terminalPkg⟩

end BEDC.Derived.CauchyModulusRefinementUp
