import BEDC.Derived.RatUp

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RatHistoryCarrier_e0_absurd {tail : BEDC.FKernel.Hist.BHist} :
    RatHistoryCarrier (BEDC.FKernel.Hist.BHist.e0 tail) -> False := by
  intro carrier
  cases carrier with
  | intro _ signData =>
      cases signData with
      | intro _ ratCarrier =>
          exact PositiveUnaryDenominator_e0_absurd
            (RatCarrier_positive_denominator ratCarrier)

theorem RatHistoryCarrier_e1_tail_unary_iff {tail : BHist} :
    RatHistoryCarrier (BHist.e1 tail) ↔ UnaryHistory tail := by
  constructor
  · intro carrier
    have positive : PositiveUnaryDenominator (BHist.e1 tail) :=
      RatHistoryCarrier_iff_positive_denominator.mp carrier
    exact PositiveUnaryDenominator_e1_iff_unary.mp positive
  · intro tailUnary
    have positive : PositiveUnaryDenominator (BHist.e1 tail) :=
      PositiveUnaryDenominator_e1_iff_unary.mpr tailUnary
    exact RatHistoryCarrier_iff_positive_denominator.mpr positive

theorem RatHistoryClassifier_append_unary_denominator_closed {d e tailD tailE : BHist} :
    RatHistoryClassifier d e -> UnaryHistory tailD -> hsame tailD tailE ->
      RatHistoryClassifier (BEDC.FKernel.Cont.append d tailD)
        (BEDC.FKernel.Cont.append e tailE) := by
  intro classifier tailDUnary tailSame
  cases classifier with
  | intro carrierD rest =>
      cases rest with
      | intro carrierE denSame =>
          have tailEUnary : UnaryHistory tailE := unary_transport tailDUnary tailSame
          have carrierDApp :
              RatHistoryCarrier (BEDC.FKernel.Cont.append d tailD) :=
            RatHistoryCarrier_append_unary_denominator_closed carrierD tailDUnary
          have carrierEApp :
              RatHistoryCarrier (BEDC.FKernel.Cont.append e tailE) :=
            RatHistoryCarrier_append_unary_denominator_closed carrierE tailEUnary
          have appendedSame :
              hsame (BEDC.FKernel.Cont.append d tailD)
                (BEDC.FKernel.Cont.append e tailE) := by
            cases denSame
            cases tailSame
            exact hsame_refl (BEDC.FKernel.Cont.append d tailD)
          exact ⟨carrierDApp, carrierEApp, appendedSame⟩

theorem RatHistoryClassifier_prepend_unary_denominator_closed {d e prefD prefE : BHist} :
    RatHistoryClassifier d e -> UnaryHistory prefD -> hsame prefD prefE ->
      RatHistoryClassifier (BEDC.FKernel.Cont.append prefD d)
        (BEDC.FKernel.Cont.append prefE e) := by
  intro classifier prefDUnary prefSame
  cases classifier with
  | intro carrierD rest =>
      cases rest with
      | intro carrierE denSame =>
          have prefEUnary : UnaryHistory prefE := unary_transport prefDUnary prefSame
          have carrierDPre :
              RatHistoryCarrier (BEDC.FKernel.Cont.append prefD d) :=
            RatHistoryCarrier_prepend_unary_denominator_closed prefDUnary carrierD
          have carrierEPre :
              RatHistoryCarrier (BEDC.FKernel.Cont.append prefE e) :=
            RatHistoryCarrier_prepend_unary_denominator_closed prefEUnary carrierE
          have prependedSame :
              hsame (BEDC.FKernel.Cont.append prefD d)
                (BEDC.FKernel.Cont.append prefE e) := by
            cases prefSame
            cases denSame
            exact hsame_refl (BEDC.FKernel.Cont.append prefD d)
          exact ⟨carrierDPre, carrierEPre, prependedSame⟩

theorem RatHistoryClassifier_unary_denominator_context_closed
    {d e prefD prefE tailD tailE : BHist} :
    RatHistoryClassifier d e -> UnaryHistory prefD -> hsame prefD prefE ->
      UnaryHistory tailD -> hsame tailD tailE ->
        RatHistoryClassifier
          (BEDC.FKernel.Cont.append prefD (BEDC.FKernel.Cont.append d tailD))
          (BEDC.FKernel.Cont.append prefE (BEDC.FKernel.Cont.append e tailE)) := by
  intro classifier prefDUnary prefSame tailDUnary tailSame
  have tailClosed :
      RatHistoryClassifier (BEDC.FKernel.Cont.append d tailD)
        (BEDC.FKernel.Cont.append e tailE) :=
    RatHistoryClassifier_append_unary_denominator_closed classifier tailDUnary tailSame
  exact RatHistoryClassifier_prepend_unary_denominator_closed tailClosed prefDUnary prefSame

theorem RatHistoryLedgerPolicy_classifier_endpoint_equivalence {rho v w : BHist} :
    RatHistoryLedgerPolicy rho v ->
      (RatHistoryClassifier rho w <-> RatHistoryClassifier v w) := by
  intro ledger
  constructor
  · intro classified
    exact RatHistoryClassifier_trans
      (RatHistoryClassifier_symm (RatHistoryLedgerPolicy_raw_visible_classifier ledger))
      classified
  · intro classified
    exact RatHistoryLedgerPolicy_classifier_extension ledger classified

end BEDC.Derived.RatUp
