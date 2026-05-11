import BEDC.Derived.DyadicRatCoreUp

namespace BEDC.Derived.DyadicRatCoreUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def DyadicRatCoreDistanceWindow
    (mantissa0 mantissa1 exponent0 exponent1 ledger0 ledger1 distance abs window : BHist) :
    Prop :=
  DyadicRatCoreCarrier mantissa0 exponent0 ledger0 BHist.Empty ∧
    DyadicRatCoreCarrier mantissa1 exponent1 ledger1 BHist.Empty ∧
      Cont ledger0 ledger1 distance ∧ Cont distance mantissa0 abs ∧
        Cont abs exponent1 window

theorem DyadicRatCoreDistanceWindow_closed_generation
    {mantissa0 mantissa1 exponent0 exponent1 ledger0 ledger1 distance abs window : BHist}
    {P : BHist -> Prop} :
    DyadicRatCoreDistanceWindow mantissa0 mantissa1 exponent0 exponent1 ledger0 ledger1
        distance abs window ->
      P BHist.Empty ->
        (forall h : BHist, UnaryHistory h -> P h -> P (BHist.e1 h)) -> P window := by
  intro windowRows base step
  rcases windowRows with
    ⟨carrier0, carrier1, distanceRow, absRow, windowRow⟩
  have ledger0Unary : UnaryHistory ledger0 :=
    carrier0.right.right.right.right
  have ledger1Unary : UnaryHistory ledger1 :=
    carrier1.right.right.right.right
  have mantissa0Unary : UnaryHistory mantissa0 :=
    (PositiveUnaryDenominator_unary_and_nonempty
      (RatHistoryCarrier_iff_positive_denominator.mp carrier0.left)).left
  have exponent1Unary : UnaryHistory exponent1 :=
    (PositiveUnaryDenominator_unary_and_nonempty carrier1.right.left).left
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed ledger0Unary ledger1Unary distanceRow
  have absUnary : UnaryHistory abs :=
    unary_cont_closed distanceUnary mantissa0Unary absRow
  have windowUnary : UnaryHistory window :=
    unary_cont_closed absUnary exponent1Unary windowRow
  exact unary_history_induction base step window windowUnary

end BEDC.Derived.DyadicRatCoreUp
