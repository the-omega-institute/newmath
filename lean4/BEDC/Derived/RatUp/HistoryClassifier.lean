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

end BEDC.Derived.RatUp
