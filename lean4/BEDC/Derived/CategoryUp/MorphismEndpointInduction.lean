import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist BEDC.FKernel.Unary

theorem CategoryHomCarrier_empty_morphism_endpoint_induction {P : BHist -> Prop}
    (base : P BHist.Empty)
    (step : forall h : BHist, UnaryHistory h -> P h -> P (BHist.e1 h)) {a b : BHist} :
    CategoryHomCarrier a b BHist.Empty -> P a ∧ P b := by
  intro homCarrier
  have data := CategoryHomCarrier_empty_identity_iff.mp homCarrier
  have sourceValue : P a := unary_history_induction base step a data.left
  have targetValue : P b := by
    cases data.right.right
    exact sourceValue
  exact And.intro sourceValue targetValue

theorem CategoryHomCarrier_morphism_induction {a b : BHist} {P : BHist -> Prop} :
    P BHist.Empty ->
      (forall f : BHist, UnaryHistory f -> P f -> P (BHist.e1 f)) ->
      forall {f : BHist}, CategoryHomCarrier a b f -> P f := by
  intro base step f homCarrier
  exact unary_history_induction base step f homCarrier.right.right.left

end BEDC.Derived.CategoryUp
