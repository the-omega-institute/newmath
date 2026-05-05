import BEDC.FKernel.Cont
import BEDC.Derived.FieldExtUp
import BEDC.Derived.FieldUp.SingletonMulEndpoint

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

end BEDC.Derived.FieldExtUp
