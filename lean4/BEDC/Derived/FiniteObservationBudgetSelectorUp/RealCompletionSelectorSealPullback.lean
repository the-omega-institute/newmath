import BEDC.Derived.FiniteObservationBudgetSelectorUp
import BEDC.Derived.RealCompletionSelectorSealUp

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RealCompletionSelectorSealUp

theorem FiniteObservationBudgetSelectorCarrier_realcompletionselectorseal_pullback
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N b' w' r' l' e' h' c' p' n' pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      RealCompletionSelectorSealCarrier b' w' r' l' e' h' c' p' n' bundle pkg ->
        hsame B b' ->
          hsame W w' ->
            hsame R r' ->
              hsame E e' ->
                Cont E e' pullback ->
                  PkgSig bundle pullback pkg ->
                    UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧
                      UnaryHistory w' ∧ UnaryHistory r' ∧ UnaryHistory e' ∧
                        UnaryHistory pullback ∧ Cont B S W ∧ Cont W D R ∧
                          Cont b' w' r' ∧ Cont r' l' e' ∧ Cont E e' pullback ∧
                            hsame B b' ∧ hsame W w' ∧ hsame R r' ∧ hsame E e' ∧
                              PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro selectorCarrier sealCarrier sameB sameW sameR sameE pullbackRoute pullbackPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, regularRoute,
    _sealRoute, _sameName⟩ := selectorCarrier
  obtain ⟨_bUnary, wUnary', rUnary', _lUnary, eUnary', _hUnary, _cUnary, _pUnary,
    _nUnary, sealBudgetRoute, sealLimitRoute, _sealPkg, _sameSealName⟩ := sealCarrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD regularRoute
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed unaryE eUnary' pullbackRoute
  exact
    ⟨unaryW, unaryR, unaryE, wUnary', rUnary', eUnary', pullbackUnary, budgetRoute,
      regularRoute, sealBudgetRoute, sealLimitRoute, pullbackRoute, sameB, sameW, sameR,
      sameE, pullbackPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp
