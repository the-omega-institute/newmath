import BEDC.Derived.FieldUp.RatContinuation

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem field_rat_denominator_context_invariant_obstruction_package
    {p p' q q' d e pd pe left right : BHist} :
    UnaryHistory p -> UnaryHistory p' -> UnaryHistory q -> UnaryHistory q' -> hsame p p' ->
      hsame q q' -> RatHistoryCarrier d -> RatHistoryCarrier e -> Cont p d pd ->
        Cont p' e pe -> Cont pd q left -> Cont pe q' right ->
          (RatHistoryClassifier d e <-> RatHistoryClassifier left right) /\
            (RatHistoryLedgerPolicy d e -> RatHistoryLedgerPolicy left right) /\
              (forall {u : BHist}, RatHistoryCarrier u ->
                ((forall {x r : BHist}, RatHistoryCarrier x -> Cont u x r ->
                    RatHistoryClassifier r x) -> False) /\
                  ((forall {x r : BHist}, RatHistoryCarrier x -> Cont x u r ->
                    RatHistoryClassifier r x) -> False)) := by
  intro prefixUnary prefixUnary' suffixUnary suffixUnary' samePrefix sameSuffix carrierD carrierE
    leftPrefix rightPrefix leftSuffix rightSuffix
  constructor
  · exact field_rat_denominator_hsame_matched_context_classifier_exactness prefixUnary
      prefixUnary' suffixUnary suffixUnary' samePrefix sameSuffix carrierD carrierE leftPrefix
      rightPrefix leftSuffix rightSuffix
  · constructor
    · intro ledger
      exact field_rat_denominator_continuation_common_context_ledger_closure ledger prefixUnary
        prefixUnary' suffixUnary suffixUnary' samePrefix sameSuffix leftPrefix rightPrefix
        leftSuffix rightSuffix
    · intro u carrierU
      exact And.intro
        (field_rat_denominator_continuation_no_internal_left_unit carrierU)
        (field_rat_denominator_continuation_no_internal_unit carrierU)

end BEDC.Derived.FieldUp
