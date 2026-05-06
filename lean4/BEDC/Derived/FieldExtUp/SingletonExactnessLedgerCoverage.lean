import BEDC.Derived.FieldExtUp.SingletonLedger

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp

theorem FieldExtSingleton_exactness_ledger_coverage {h r m a : BHist}
    (p : FieldSingletonNonZero a) :
    FieldExtSingletonLedgerPolicy h -> FieldSingletonCarrier r -> VecSpaceSingletonCarrier m ->
      FieldSingletonClassifier (FieldExtSingletonEmbedding h) (append BHist.Empty h) ∧
        FieldSingletonClassifier FieldSingletonZero BHist.Empty ∧
          FieldSingletonClassifier FieldSingletonOne BHist.Empty ∧
            FieldSingletonClassifier (FieldSingletonAdd r m) BHist.Empty ∧
              FieldSingletonClassifier (FieldSingletonNeg r) BHist.Empty ∧
                FieldSingletonClassifier (FieldSingletonMul r m) BHist.Empty ∧
                  FieldSingletonClassifier (FieldSingletonInv a p) FieldSingletonZero ∧
                    VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) BHist.Empty := by
  intro policy carrierR carrierM
  have policyRows := FieldExtSingletonLedgerPolicy_carrier_coincidence policy
  have operationRows := FieldExtSingletonOperation_readback_exactness carrierR carrierM
  have inverseRow : FieldSingletonClassifier (FieldSingletonInv a p) FieldSingletonZero := by
    unfold FieldSingletonInv FieldSingletonZero
    exact operationRows.left
  exact And.intro policyRows.right.right
    (And.intro operationRows.left
      (And.intro operationRows.right.left
        (And.intro operationRows.right.right.left
          (And.intro operationRows.right.right.right.left
            (And.intro operationRows.right.right.right.right.left
              (And.intro inverseRow operationRows.right.right.right.right.right.left))))))

end BEDC.Derived.FieldExtUp
