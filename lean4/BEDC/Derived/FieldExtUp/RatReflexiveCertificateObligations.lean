import BEDC.Derived.FieldExtUp.RatReflexiveOperationTable
import BEDC.Derived.FieldExtUp.RatReflexiveSemanticCertificate
import BEDC.Derived.FieldExtUp.RatReflexiveEmbedding

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp

theorem FieldExtRatReflexive_certificate_obligations {h k r r' m m' product action : BHist} :
    RatHistoryClassifier h k -> RatHistoryClassifier r r' -> RatHistoryClassifier m m' ->
      Cont r m product -> Cont (FieldExtSingletonEmbedding r') m' action ->
        SemanticNameCert RatHistoryCarrier
          (fun x : BHist => RatHistoryCarrier x ∧
            RatHistoryCarrier (FieldExtSingletonEmbedding x))
          (fun x : BHist => RatHistoryLedgerPolicy x (FieldExtSingletonEmbedding x))
          RatHistoryClassifier ∧
          RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
            RatHistoryLedgerPolicy k (FieldExtSingletonEmbedding k) ∧
              RatHistoryClassifier product action ∧
                RatHistoryCarrier product ∧
                  RatHistoryCarrier action ∧
                    RatHistoryClassifier (FieldExtSingletonEmbedding r') r' := by
  intro classifiedHK classifiedRR classifiedMM productCont actionCont
  have ledgerRows := FieldExtRatReflexiveEmbedding_ledger_source_lock classifiedHK
  have operationRows :=
    FieldExtRatReflexive_operation_table_source_coverage
      classifiedRR classifiedMM productCont actionCont
  exact And.intro FieldExtRatReflexive_semantic_name_certificate
    (And.intro ledgerRows.left
      (And.intro ledgerRows.right.left
        (And.intro operationRows.left
          (And.intro operationRows.right.left
            (And.intro operationRows.right.right.left operationRows.right.right.right)))))

theorem FieldExtRatReflexive_source_pattern_classifier_obligations {h k : BHist} :
    RatHistoryClassifier h k ->
      FieldExtRatReflexiveCarrier h ∧ FieldExtRatReflexiveCarrier k ∧
        RatHistoryClassifier (FieldExtSingletonEmbedding h) (FieldExtSingletonEmbedding k) ∧
          Cont BHist.Empty h (FieldExtSingletonEmbedding h) ∧
            Cont BHist.Empty k (FieldExtSingletonEmbedding k) := by
  intro classified
  have carrierH : FieldExtRatReflexiveCarrier h :=
    FieldExtRatReflexiveCarrier_rat_history_closure classified.left
  have carrierK : FieldExtRatReflexiveCarrier k :=
    FieldExtRatReflexiveCarrier_rat_history_closure classified.right.left
  have lock := FieldExtRatReflexive_source_pattern_lock classified
  exact And.intro carrierH
    (And.intro carrierK
      (And.intro lock.right.right.left
        (And.intro lock.right.right.right.left lock.right.right.right.right)))

end BEDC.Derived.FieldExtUp
