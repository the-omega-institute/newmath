import BEDC.Derived.FieldExtUp.RatReflexiveOperationTable
import BEDC.Derived.FieldExtUp.RatReflexiveSemanticCertificate

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

end BEDC.Derived.FieldExtUp
