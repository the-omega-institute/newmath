import BEDC.Derived.FiniteObservationBudgetSelectorUp
import BEDC.Derived.RealTailAgreementSealUp.TasteGate

namespace BEDC.Derived.FiniteObservationBudgetSelectorUp.RealTailAgreementSealPullback

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.RealTailAgreementSealUp

theorem FiniteObservationBudgetSelectorCarrier_realtailagreementseal_pullback
    [AskSetup] [PackageSetup]
    {B S W D R E H C P N R0 S0 WQ DQ AQ HQ CQ PQ NQ pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteObservationBudgetSelectorCarrier B S W D R E H C P N ->
      RealTailAgreementSealCarrier R0 S0 WQ DQ AQ HQ CQ PQ NQ ->
        hsame W WQ ->
          hsame D DQ ->
            hsame R R0 ->
              Cont E AQ pullback ->
                PkgSig bundle pullback pkg ->
                  UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory E ∧
                    UnaryHistory WQ ∧ UnaryHistory DQ ∧ UnaryHistory R0 ∧ UnaryHistory AQ ∧
                      UnaryHistory pullback ∧ Cont B S W ∧ Cont W D R ∧
                        Cont E AQ pullback ∧ hsame W WQ ∧ hsame D DQ ∧ hsame R R0 ∧
                          PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro selectorCarrier sealCarrier sameWindow sameDyadic sameRegular pullbackRoute pullbackPkg
  obtain ⟨unaryB, unaryS, unaryD, unaryE, _unaryH, budgetRoute, dyadicRoute,
    _sealRoute, _sameName⟩ := selectorCarrier
  obtain ⟨unaryR0, _unaryS0, unaryWQ, unaryDQ, unaryAQ, _unaryHQ, _unaryCQ,
    _unaryPQ, _unaryNQ, _sealWindowRoute, _sealAgreementRoute, _sealNameRoute,
    _sameProvenance⟩ := sealCarrier
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryB unaryS budgetRoute
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryW unaryD dyadicRoute
  have unaryPullback : UnaryHistory pullback :=
    unary_cont_closed unaryE unaryAQ pullbackRoute
  exact
    ⟨unaryW, unaryD, unaryR, unaryE, unaryWQ, unaryDQ, unaryR0, unaryAQ, unaryPullback,
      budgetRoute, dyadicRoute, pullbackRoute, sameWindow, sameDyadic, sameRegular,
      pullbackPkg⟩

end BEDC.Derived.FiniteObservationBudgetSelectorUp.RealTailAgreementSealPullback
