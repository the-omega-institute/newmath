import BEDC.Derived.RatUp.LedgerContextEquivalence

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem RatHistoryLedgerPolicy_cont_unary_context_e1_pair_readback
    {raw visible prefRaw prefVisible tailRaw tailVisible midRaw midVisible outRaw outVisible
      leftTail rightTail : BHist} :
    RatHistoryLedgerPolicy raw visible -> UnaryHistory prefRaw -> hsame prefRaw prefVisible ->
      UnaryHistory tailRaw -> hsame tailRaw tailVisible -> Cont prefRaw raw midRaw ->
        Cont midRaw tailRaw outRaw -> Cont prefVisible visible midVisible ->
          Cont midVisible tailVisible outVisible -> hsame outRaw (BHist.e1 leftTail) ->
            hsame outVisible (BHist.e1 rightTail) ->
              UnaryHistory leftTail ∧ UnaryHistory rightTail ∧ hsame leftTail rightTail := by
  intro ledger prefUnary samePref tailUnary sameTail prefRawCont outRawCont prefVisibleCont
    outVisibleCont sameRawEndpoint sameVisibleEndpoint
  have endpointEquiv :
      RatHistoryClassifier outRaw (BHist.e1 rightTail) <->
        RatHistoryClassifier outVisible (BHist.e1 rightTail) :=
    RatHistoryLedgerPolicy_cont_unary_context_classifier_endpoint_equivalence ledger
      prefUnary samePref tailUnary sameTail prefRawCont outRawCont prefVisibleCont
      outVisibleCont
  have visibleCarrier : RatHistoryCarrier outVisible :=
    RatHistoryLedgerPolicy_visible_carrier
      (RatHistoryLedgerPolicy_hsame_transport
        (RatHistoryLedgerPolicy_unary_denominator_context_closed ledger prefUnary samePref
          tailUnary sameTail)
        (hsame_trans (hsame_symm (append_assoc prefRaw raw tailRaw))
          (Eq.trans outRawCont
            (congrArg (fun h : BHist => append h tailRaw) prefRawCont)).symm)
        (hsame_trans (hsame_symm (append_assoc prefVisible visible tailVisible))
          (Eq.trans outVisibleCont
            (congrArg (fun h : BHist => append h tailVisible) prefVisibleCont)).symm))
  have visibleSelf : RatHistoryClassifier outVisible outVisible :=
    ⟨visibleCarrier, visibleCarrier, hsame_refl outVisible⟩
  have visibleTarget : RatHistoryClassifier outVisible (BHist.e1 rightTail) :=
    RatHistoryClassifier_hsame_transport (hsame_refl outVisible) sameVisibleEndpoint visibleSelf
  have rawTarget : RatHistoryClassifier outRaw (BHist.e1 rightTail) :=
    endpointEquiv.mpr visibleTarget
  have displayed : RatHistoryClassifier (BHist.e1 leftTail) (BHist.e1 rightTail) :=
    RatHistoryClassifier_hsame_transport sameRawEndpoint (hsame_refl (BHist.e1 rightTail))
      rawTarget
  exact RatHistoryClassifier_e1_tail_unary_iff.mp displayed

theorem RatHistoryLedgerPolicy_cont_unary_context_e0_endpoint_absurd
    {raw visible prefRaw prefVisible tailRaw tailVisible midRaw midVisible outRaw outVisible
      leftZero rightZero : BHist} :
    RatHistoryLedgerPolicy raw visible -> UnaryHistory prefRaw -> hsame prefRaw prefVisible ->
      UnaryHistory tailRaw -> hsame tailRaw tailVisible -> Cont prefRaw raw midRaw ->
        Cont midRaw tailRaw outRaw -> Cont prefVisible visible midVisible ->
          Cont midVisible tailVisible outVisible ->
            (hsame outRaw (BHist.e0 leftZero) -> False) ∧
              (hsame outVisible (BHist.e0 rightZero) -> False) := by
  intro ledger prefUnary samePref tailUnary sameTail prefRawCont outRawCont prefVisibleCont
    outVisibleCont
  have positives :
      PositiveUnaryDenominator outRaw ∧ PositiveUnaryDenominator outVisible :=
    RatHistoryLedgerPolicy_cont_unary_context_positive_denominators ledger prefUnary samePref
      tailUnary sameTail prefRawCont outRawCont prefVisibleCont outVisibleCont
  constructor
  · intro sameRawZero
    exact PositiveUnaryDenominator_e0_absurd
      (PositiveUnaryDenominator_hsame_transport sameRawZero positives.left)
  · intro sameVisibleZero
    exact PositiveUnaryDenominator_e0_absurd
      (PositiveUnaryDenominator_hsame_transport sameVisibleZero positives.right)

theorem RatHistoryLedgerPolicy_cont_unary_context_empty_endpoint_absurd
    {raw visible prefRaw prefVisible tailRaw tailVisible midRaw midVisible outRaw outVisible :
      BHist} :
    RatHistoryLedgerPolicy raw visible -> UnaryHistory prefRaw -> hsame prefRaw prefVisible ->
      UnaryHistory tailRaw -> hsame tailRaw tailVisible -> Cont prefRaw raw midRaw ->
        Cont midRaw tailRaw outRaw -> Cont prefVisible visible midVisible ->
          Cont midVisible tailVisible outVisible ->
            (hsame outRaw BHist.Empty -> False) ∧ (hsame outVisible BHist.Empty -> False) := by
  intro ledger prefUnary samePref tailUnary sameTail prefRawCont outRawCont prefVisibleCont
    outVisibleCont
  have positives : PositiveUnaryDenominator outRaw ∧ PositiveUnaryDenominator outVisible :=
    RatHistoryLedgerPolicy_cont_unary_context_positive_denominators ledger prefUnary samePref
      tailUnary sameTail prefRawCont outRawCont prefVisibleCont outVisibleCont
  exact And.intro (PositiveUnaryDenominator_not_empty positives.left)
    (PositiveUnaryDenominator_not_empty positives.right)

end BEDC.Derived.RatUp
