import BEDC.Derived.FieldExtUp.RatReflexiveOperationTable

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp

theorem FieldExtRatReflexive_public_name_certificate :
    SemanticNameCert RatHistoryCarrier
        (fun h : BHist => RatHistoryCarrier (FieldExtSingletonEmbedding h))
        (fun h : BHist => RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h))
        RatHistoryClassifier ∧
      (forall {h k : BHist}, RatHistoryClassifier h k ->
        RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k)) ∧
      (forall {r m out product : BHist}, RatHistoryCarrier r -> RatHistoryCarrier m ->
        Cont (FieldExtSingletonEmbedding r) m out -> Cont r m product ->
          RatHistoryClassifier out product) := by
  have semantic :
      SemanticNameCert RatHistoryCarrier
        (fun h : BHist => RatHistoryCarrier (FieldExtSingletonEmbedding h))
        (fun h : BHist => RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h))
        RatHistoryClassifier := {
    core := rat_history_semantic_name_certificate.core
    pattern_sound := by
      intro h source
      unfold FieldExtSingletonEmbedding
      exact RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left h)) source
    ledger_sound := by
      intro h source
      unfold FieldExtSingletonEmbedding
      exact And.intro source (hsame_symm (append_empty_left h))
  }
  exact And.intro semantic
    (And.intro
      (by
        intro h k classified
        exact (FieldExtRatReflexive_exact_endpoint_classification classified).right.right)
      (by
        intro r m out product carrierR carrierM actionCont productCont
        exact (FieldExtRatReflexive_scalar_action_readback carrierR carrierM actionCont
          productCont).left))

end BEDC.Derived.FieldExtUp
