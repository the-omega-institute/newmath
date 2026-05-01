import BEDC.Derived.RatUp.HistoryClassifier

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary

theorem PositiveUnaryDenominator_append_unary_context {pref den tail : BHist} :
    UnaryHistory pref → PositiveUnaryDenominator den → UnaryHistory tail →
      PositiveUnaryDenominator
        (BEDC.FKernel.Cont.append pref (BEDC.FKernel.Cont.append den tail)) := by
  intro prefUnary positive tailUnary
  exact PositiveUnaryDenominator_append_unary_prefix prefUnary
    (PositiveUnaryDenominator_append_unary_tail positive tailUnary)

theorem RatCarrier_unary_denominator_context_closed {sign : BMark}
    {numerator denominator pref tail : BHist} :
    UnaryHistory pref -> RatCarrier sign numerator denominator -> UnaryHistory tail ->
      RatCarrier sign numerator
        (BEDC.FKernel.Cont.append pref (BEDC.FKernel.Cont.append denominator tail)) := by
  intro prefUnary carrier tailUnary
  exact RatCarrier_prepend_unary_denominator_closed prefUnary
    (RatCarrier_append_unary_denominator_closed carrier tailUnary)

theorem RatHistoryCarrier_unary_denominator_context_closed {d pref tail : BHist} :
    UnaryHistory pref → RatHistoryCarrier d → UnaryHistory tail →
      RatHistoryCarrier (BEDC.FKernel.Cont.append pref (BEDC.FKernel.Cont.append d tail)) := by
  intro prefUnary carrier tailUnary
  cases carrier with
  | intro sign signData =>
      cases signData with
      | intro numerator ratCarrier =>
          exact
            ⟨sign, numerator,
              RatCarrier_unary_denominator_context_closed prefUnary ratCarrier tailUnary⟩

theorem RatClassifierSpec_append_unary_denominator_context_closed {s1 s2 : BMark}
    {n1 n2 d1 d2 pref1 pref2 tail1 tail2 : BHist} :
    RatClassifierSpec s1 n1 d1 s2 n2 d2 -> UnaryHistory pref1 -> hsame pref1 pref2 ->
      UnaryHistory tail1 -> hsame tail1 tail2 ->
        RatClassifierSpec s1 n1
          (BEDC.FKernel.Cont.append pref1 (BEDC.FKernel.Cont.append d1 tail1))
          s2 n2
          (BEDC.FKernel.Cont.append pref2 (BEDC.FKernel.Cont.append d2 tail2)) := by
  intro classifier pref1Unary samePref tail1Unary sameTail
  exact
    RatClassifierSpec_prepend_unary_denominators_closed
      (RatClassifierSpec_append_unary_denominators_closed classifier tail1Unary sameTail)
      pref1Unary samePref

theorem RatHistoryLedgerPolicy_unary_denominator_context_closed
    {raw visible prefRaw prefVisible tailRaw tailVisible : BHist} :
    RatHistoryLedgerPolicy raw visible -> UnaryHistory prefRaw -> hsame prefRaw prefVisible ->
      UnaryHistory tailRaw -> hsame tailRaw tailVisible ->
        RatHistoryLedgerPolicy
          (BEDC.FKernel.Cont.append prefRaw (BEDC.FKernel.Cont.append raw tailRaw))
          (BEDC.FKernel.Cont.append prefVisible (BEDC.FKernel.Cont.append visible tailVisible)) := by
  intro ledger prefRawUnary samePref tailRawUnary sameTail
  have appended :
      RatHistoryLedgerPolicy (BEDC.FKernel.Cont.append raw tailRaw)
        (BEDC.FKernel.Cont.append visible tailVisible) :=
    RatHistoryLedgerPolicy_append_unary_denominator_closed ledger tailRawUnary sameTail
  exact RatHistoryLedgerPolicy_prepend_unary_denominator_closed appended prefRawUnary samePref

end BEDC.Derived.RatUp
