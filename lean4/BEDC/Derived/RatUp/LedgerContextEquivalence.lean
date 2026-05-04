import BEDC.Derived.RatUp.DenominatorContext

namespace BEDC.Derived.RatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem RatHistoryLedgerPolicy_shared_raw_context_visible_endpoint_equivalence
    {raw visible visible' pref prefVisible prefVisible' tail tailVisible tailVisible' w :
      BHist} :
    RatHistoryLedgerPolicy raw visible -> RatHistoryLedgerPolicy raw visible' ->
      UnaryHistory pref -> hsame pref prefVisible -> hsame pref prefVisible' ->
        UnaryHistory tail -> hsame tail tailVisible -> hsame tail tailVisible' ->
          (RatHistoryClassifier (append prefVisible (append visible tailVisible)) w <->
            RatHistoryClassifier (append prefVisible' (append visible' tailVisible')) w) := by
  intro leftLedger rightLedger prefUnary samePrefLeft samePrefRight tailUnary sameTailLeft
    sameTailRight
  have leftContextLedger :
      RatHistoryLedgerPolicy (append pref (append raw tail))
        (append prefVisible (append visible tailVisible)) :=
    RatHistoryLedgerPolicy_unary_denominator_context_closed leftLedger prefUnary samePrefLeft
      tailUnary sameTailLeft
  have rightContextLedger :
      RatHistoryLedgerPolicy (append pref (append raw tail))
        (append prefVisible' (append visible' tailVisible')) :=
    RatHistoryLedgerPolicy_unary_denominator_context_closed rightLedger prefUnary samePrefRight
      tailUnary sameTailRight
  have endpoints :
      RatHistoryClassifier (append prefVisible (append visible tailVisible))
        (append prefVisible' (append visible' tailVisible')) :=
    RatHistoryLedgerPolicy_shared_raw_visible_classifier leftContextLedger rightContextLedger
  constructor
  · intro classified
    exact RatHistoryClassifier_trans (RatHistoryClassifier_symm endpoints) classified
  · intro classified
    exact RatHistoryClassifier_trans endpoints classified

theorem RatHistoryLedgerPolicy_cont_unary_context_classifier_endpoint_equivalence
    {raw visible prefRaw prefVisible tailRaw tailVisible midRaw midVisible outRaw outVisible w :
      BHist} :
    RatHistoryLedgerPolicy raw visible -> UnaryHistory prefRaw -> hsame prefRaw prefVisible ->
      UnaryHistory tailRaw -> hsame tailRaw tailVisible -> Cont prefRaw raw midRaw ->
        Cont midRaw tailRaw outRaw -> Cont prefVisible visible midVisible ->
          Cont midVisible tailVisible outVisible ->
            (RatHistoryClassifier outRaw w <-> RatHistoryClassifier outVisible w) := by
  intro ledger prefUnary samePref tailUnary sameTail prefRawCont outRawCont prefVisibleCont
    outVisibleCont
  have contextLedger :
      RatHistoryLedgerPolicy (append prefRaw (append raw tailRaw))
        (append prefVisible (append visible tailVisible)) :=
    RatHistoryLedgerPolicy_unary_denominator_context_closed ledger prefUnary samePref tailUnary
      sameTail
  have sameOutRaw : hsame (append prefRaw (append raw tailRaw)) outRaw := by
    have outEq : outRaw = append (append prefRaw raw) tailRaw :=
      Eq.trans outRawCont (congrArg (fun h : BHist => append h tailRaw) prefRawCont)
    exact hsame_trans (hsame_symm (append_assoc prefRaw raw tailRaw)) outEq.symm
  have sameOutVisible : hsame (append prefVisible (append visible tailVisible)) outVisible := by
    have outEq : outVisible = append (append prefVisible visible) tailVisible :=
      Eq.trans outVisibleCont
        (congrArg (fun h : BHist => append h tailVisible) prefVisibleCont)
    exact hsame_trans (hsame_symm (append_assoc prefVisible visible tailVisible)) outEq.symm
  have displayedLedger : RatHistoryLedgerPolicy outRaw outVisible :=
    RatHistoryLedgerPolicy_hsame_transport contextLedger sameOutRaw sameOutVisible
  exact RatHistoryLedgerPolicy_classifier_endpoint_equivalence displayedLedger

end BEDC.Derived.RatUp
