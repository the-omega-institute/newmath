import BEDC.Derived.FieldExtUp.RatReflexive
import BEDC.Derived.FieldExtUp.RatReflexiveSourcePattern

namespace BEDC.Derived.NumFieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.FieldExtUp
open BEDC.Derived.RatUp

theorem NumFieldReflexiveRational_finite_extension_witness {m coord : BHist} :
    RatHistoryCarrier m -> Cont m BHist.Empty coord ->
      RatHistoryClassifier coord m ∧ RatHistoryCarrier (FieldExtSingletonEmbedding m) ∧
        RatHistoryClassifier (FieldExtSingletonEmbedding m) m := by
  intro carrierM coordinateReadback
  have sameCoordM : hsame coord m :=
    cont_right_unit_result coordinateReadback
  have coordCarrier : RatHistoryCarrier coord :=
    RatHistoryCarrier_hsame_transport (hsame_symm sameCoordM) carrierM
  have coordClassifier : RatHistoryClassifier coord m :=
    And.intro coordCarrier (And.intro carrierM sameCoordM)
  have embeddedCarrier : RatHistoryCarrier (FieldExtSingletonEmbedding m) := by
    unfold FieldExtSingletonEmbedding
    exact RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left m)) carrierM
  have embeddedClassifier : RatHistoryClassifier (FieldExtSingletonEmbedding m) m := by
    unfold FieldExtSingletonEmbedding
    exact And.intro embeddedCarrier (And.intro carrierM (append_empty_left m))
  exact And.intro coordClassifier (And.intro embeddedCarrier embeddedClassifier)

theorem NumFieldRatReflexive_namecert_obligations {h k r m coord action product : BHist} :
    RatHistoryClassifier h k -> RatHistoryCarrier r -> RatHistoryCarrier m ->
      Cont m BHist.Empty coord -> Cont (FieldExtSingletonEmbedding r) m action ->
        Cont r m product ->
          SemanticNameCert RatHistoryCarrier
              (fun z : BHist => RatHistoryCarrier (FieldExtSingletonEmbedding z))
              (fun z : BHist => RatHistoryLedgerPolicy z (FieldExtSingletonEmbedding z))
              RatHistoryClassifier ∧
            RatHistoryClassifier coord m ∧
              RatHistoryClassifier product action ∧
                RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h) ∧
                  RatHistoryLedgerPolicy k (FieldExtSingletonEmbedding k) := by
  intro classifiedHK carrierR carrierM coordReadback actionCont productCont
  have fieldExtRows := FieldExtRatReflexive_public_name_certificate
  have coordRows :=
    NumFieldReflexiveRational_finite_extension_witness carrierM coordReadback
  have ledgerRows :=
    FieldExtRatReflexive_ledger_provenance classifiedHK carrierR carrierM productCont actionCont
  exact And.intro fieldExtRows.left
    (And.intro coordRows.left
      (And.intro ledgerRows.right.right.left
        (And.intro ledgerRows.left ledgerRows.right.left)))

end BEDC.Derived.NumFieldUp
