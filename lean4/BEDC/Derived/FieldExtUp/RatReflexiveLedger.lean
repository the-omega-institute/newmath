import BEDC.Derived.FieldExtUp.RatReflexiveOperationTable

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem FieldExtRatReflexive_ledger_standard_bridge_obligations {h r m out : BHist} :
    RatHistoryCarrier h -> RatHistoryCarrier r -> RatHistoryCarrier m -> Cont r m out ->
      RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
        RatHistoryClassifier (FieldExtSingletonEmbedding h) h ∧
          RatHistoryClassifier out (append r m) ∧
            Cont BHist.Empty h (FieldExtSingletonEmbedding h) := by
  intro carrierH carrierR carrierM continuation
  have selfClassified : RatHistoryClassifier h h :=
    And.intro carrierH (And.intro carrierH (hsame_refl h))
  have sourceLock := FieldExtRatReflexiveEmbedding_ledger_source_lock selfClassified
  have actionReadback :
      RatHistoryClassifier out (append r m) :=
    FieldExtRatReflexiveTower_scalar_action carrierR carrierM continuation
  exact And.intro sourceLock.left
    (And.intro (FieldExtRatReflexive_exact_endpoint_classification selfClassified).left
      (And.intro actionReadback sourceLock.right.right.right.left))

end BEDC.Derived.FieldExtUp
