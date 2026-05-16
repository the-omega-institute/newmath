import BEDC.Derived.ObserverFilterBudgetSelectorUp.TasteGate
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObserverFilterBudgetSelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ObserverFilterBudgetSelectorCarrier
    (identity filter selected budget window dyadic regular realSeal omitted transport route
      provenance nameRow : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist BMark
  observerFilterBudgetSelectorFields
      (ObserverFilterBudgetSelectorUp.mk filter identity selected omitted budget window dyadic
        regular realSeal transport route provenance nameRow) =
    [filter, identity, selected, omitted, budget, window, dyadic, regular, realSeal, transport,
      route, provenance, nameRow] ∧
    UnaryHistory identity ∧ UnaryHistory filter ∧ UnaryHistory selected ∧
      UnaryHistory budget ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
        UnaryHistory regular ∧ UnaryHistory realSeal ∧ UnaryHistory omitted ∧
          UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
            UnaryHistory nameRow ∧ Cont selected budget window ∧
              Cont window dyadic regular ∧ Cont transport route provenance

theorem ObserverFilterBudgetSelectorCarrier_real_completion_consumer
    {identity filter selected budget window dyadic regular realSeal omitted transport route
      provenance nameRow completionRead : BHist} :
    ObserverFilterBudgetSelectorCarrier identity filter selected budget window dyadic regular
        realSeal omitted transport route provenance nameRow →
      Cont regular realSeal completionRead →
        UnaryHistory selected ∧ UnaryHistory budget ∧ UnaryHistory window ∧
          UnaryHistory dyadic ∧ UnaryHistory regular ∧ UnaryHistory realSeal ∧
            UnaryHistory completionRead ∧ Cont selected budget window ∧
              Cont window dyadic regular ∧ Cont regular realSeal completionRead ∧
                Cont transport route provenance := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier regularRealSealCompletion
  obtain ⟨_fieldAlignment, _identityUnary, _filterUnary, selectedUnary, budgetUnary,
    windowUnary, dyadicUnary, regularUnary, realSealUnary, _omittedUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, selectedBudgetWindow,
    windowDyadicRegular, transportRouteProvenance⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed regularUnary realSealUnary regularRealSealCompletion
  exact
    ⟨selectedUnary, budgetUnary, windowUnary, dyadicUnary, regularUnary, realSealUnary,
      completionUnary, selectedBudgetWindow, windowDyadicRegular, regularRealSealCompletion,
      transportRouteProvenance⟩

end BEDC.Derived.ObserverFilterBudgetSelectorUp
