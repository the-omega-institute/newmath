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

theorem FieldExtSingleton_ledger_provenance {h : BHist} :
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

end BEDC.Derived.FieldExtUp
