import BEDC.FKernel.Cont
import BEDC.Derived.FieldExtUp
import BEDC.Derived.FieldUp.SingletonMulEndpoint

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp

theorem FieldExtSingleton_exact_endpoint_ledger {h r m : BHist} :
    FieldExtSingletonLedgerPolicy h -> FieldSingletonCarrier r -> VecSpaceSingletonCarrier m ->
      FieldSingletonClassifier (FieldExtSingletonEmbedding h) BHist.Empty ∧
        FieldSingletonClassifier FieldSingletonZero BHist.Empty ∧
          FieldSingletonClassifier FieldSingletonOne BHist.Empty ∧
            FieldSingletonClassifier (FieldSingletonAdd r m) BHist.Empty ∧
              FieldSingletonClassifier (FieldSingletonNeg r) BHist.Empty ∧
                FieldSingletonClassifier (FieldSingletonMul r m) BHist.Empty ∧
                  VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) BHist.Empty ∧
                    FieldSingletonClassifier (FieldExtSingletonEmbedding h)
                      (append BHist.Empty h) := by
  intro policy carrierR carrierM
  have policyRows := FieldExtSingletonLedgerPolicy_carrier_coincidence policy
  have exactRows :=
    FieldExtSingleton_exact_endpoint_classification policyRows.left carrierR carrierM
  exact And.intro exactRows.left
    (And.intro exactRows.right.left
      (And.intro exactRows.right.right.left
        (And.intro exactRows.right.right.right.left
          (And.intro exactRows.right.right.right.right.left
            (And.intro exactRows.right.right.right.right.right.left
              (And.intro exactRows.right.right.right.right.right.right
                policyRows.right.right))))))

theorem FieldExtSingleton_certificate_projections :
    SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
        FieldSingletonClassifier ∧
      SemanticNameCert VecSpaceSingletonCarrier VecSpaceSingletonCarrier
        VecSpaceSingletonCarrier VecSpaceSingletonClassifier ∧
      (forall {h : BHist}, FieldSingletonCarrier h ->
        FieldSingletonClassifier (FieldExtSingletonEmbedding h) h) ∧
      (forall {r m : BHist}, FieldSingletonCarrier r -> VecSpaceSingletonCarrier m ->
        FieldSingletonClassifier (FieldSingletonMul (FieldExtSingletonEmbedding r) m)
          (VecSpaceSingletonSmul (FieldExtSingletonEmbedding r) m)) := by
  have fieldCert :
      SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
        FieldSingletonClassifier :=
    singleton_empty_history_field_schema_laws.left
  have vecCert :
      SemanticNameCert VecSpaceSingletonCarrier VecSpaceSingletonCarrier
        VecSpaceSingletonCarrier VecSpaceSingletonClassifier :=
    VecSpaceSingleton_semanticNameCert
  exact And.intro fieldCert
    (And.intro vecCert
      (And.intro
        (by
          intro h carrierH
          have embeddedCarrier : FieldSingletonCarrier (FieldExtSingletonEmbedding h) := by
            unfold FieldExtSingletonEmbedding
            exact hsame_trans (append_empty_left h) carrierH
          have sameEmbedded : hsame (FieldExtSingletonEmbedding h) h := by
            unfold FieldExtSingletonEmbedding
            exact append_empty_left h
          exact And.intro embeddedCarrier (And.intro carrierH sameEmbedded))
        (by
          intro r m carrierR carrierM
          have compatible :=
            FieldExtSingletonVectorSpace_smul_mul_compatible carrierR carrierM
          exact And.intro compatible.right.left
            (And.intro compatible.left (hsame_symm compatible.right.right)))))

theorem FieldExtSingletonLedgerPolicy_ledger_provenance {h : BHist} :
    FieldExtSingletonLedgerPolicy h ->
      SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
          FieldSingletonClassifier ∧
        SemanticNameCert VecSpaceSingletonCarrier VecSpaceSingletonCarrier VecSpaceSingletonCarrier
          VecSpaceSingletonClassifier ∧
          FieldSingletonClassifier (FieldExtSingletonEmbedding h) (append BHist.Empty h) ∧
            Cont BHist.Empty h (FieldExtSingletonEmbedding h) := by
  intro policy
  have certificates := FieldExtSingleton_certificate_obligation_package
  have policyRows := FieldExtSingletonLedgerPolicy_carrier_coincidence policy
  have embeddingCont : Cont BHist.Empty h (FieldExtSingletonEmbedding h) := by
    unfold FieldExtSingletonEmbedding
    exact cont_intro rfl
  exact And.intro certificates.left
    (And.intro certificates.right.left
      (And.intro policyRows.right.right embeddingCont))

theorem FieldExtSingleton_ledger_provenance :
    SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
        FieldSingletonClassifier ∧
      SemanticNameCert VecSpaceSingletonCarrier VecSpaceSingletonCarrier VecSpaceSingletonCarrier
        VecSpaceSingletonClassifier ∧
        (forall {h : BHist}, FieldSingletonCarrier h ->
          FieldSingletonClassifier (FieldExtSingletonEmbedding h) BHist.Empty ∧
            Cont BHist.Empty h (FieldExtSingletonEmbedding h)) ∧
          (forall {r m : BHist}, FieldSingletonCarrier r -> VecSpaceSingletonCarrier m ->
            FieldSingletonClassifier (FieldSingletonMul r m) BHist.Empty ∧
              VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) BHist.Empty) := by
  constructor
  · exact singleton_empty_history_field_schema_laws.left
  · constructor
    · exact VecSpaceSingleton_semanticNameCert
    · constructor
      · intro h carrierH
        have embeddedCarrier : FieldSingletonCarrier (FieldExtSingletonEmbedding h) := by
          unfold FieldExtSingletonEmbedding
          exact hsame_trans (append_empty_left h) carrierH
        have embeddedEndpoint :
            FieldSingletonClassifier (FieldExtSingletonEmbedding h) BHist.Empty :=
          And.intro embeddedCarrier
            (And.intro (hsame_refl BHist.Empty) embeddedCarrier)
        have embeddedCont : Cont BHist.Empty h (FieldExtSingletonEmbedding h) := by
          unfold FieldExtSingletonEmbedding
          exact cont_intro rfl
        exact And.intro embeddedEndpoint embeddedCont
      · intro r m carrierR carrierM
        have rows := FieldExtSingleton_exact_endpoint_classification carrierR carrierR carrierM
        exact And.intro rows.right.right.right.right.right.left
          rows.right.right.right.right.right.right

end BEDC.Derived.FieldExtUp
