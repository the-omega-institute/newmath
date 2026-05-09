import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem SOneComponentClassifier_public_endpoint_exactness
    {x y e p x' y' e' p' : BHist} :
    SOneComponentClassifier x y e p x' y' e' p' ->
      hsame e e' ∧ hsame p p' ∧ SOneProductHistoryCarrier p' ∧
        hsame e' SOneUnitHistory ∧
          ∃ dx dy : BHist,
            hsame x' (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧
              hsame y' (BHist.e1 dy) ∧ RatHistoryCarrier dy ∧ Cont x' y' p' := by
  intro classifier
  have ledgers :=
    SOneHistoryCarrier_component_classifier_ledger_determinacy classifier.left
      classifier.right.left classifier.right.right.left classifier.right.right.right
  have readback := SOneHistoryCarrier_public_readback classifier.right.left
  exact And.intro ledgers.left (And.intro ledgers.right readback)

end BEDC.Derived.S1Up
