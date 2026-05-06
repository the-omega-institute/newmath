import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

theorem SOneComponentClassifier_visible_source_unit_equation_package
    {dx dy equationTail t x' y' e' p' : BHist} :
    SOneComponentClassifier (BHist.e1 dx) (BHist.e1 dy) (BHist.e1 equationTail)
      (BHist.e1 t) x' y' e' p' ->
      (RatHistoryCarrier dx ∧ RatHistoryCarrier dy ∧
        RatHistoryClassifier equationTail (BHist.e1 BHist.Empty) ∧
          Cont (BHist.e1 dx) dy t) ∧
        (hsame (BHist.e1 equationTail) e' ∧ hsame (BHist.e1 t) p') ∧
          (SOneProductHistoryCarrier p' ∧ hsame e' SOneUnitHistory ∧
            ∃ dx' dy' : BHist,
              hsame x' (BHist.e1 dx') ∧ RatHistoryCarrier dx' ∧
                hsame y' (BHist.e1 dy') ∧ RatHistoryCarrier dy' ∧ Cont x' y' p') := by
  intro classifier
  have sourceReadback :=
    SOneHistoryCarrier_e1_components_unit_equation_classifier classifier.left
  have ledgerDeterminacy :=
    SOneHistoryCarrier_component_classifier_ledger_determinacy classifier.left
      classifier.right.left classifier.right.right.left classifier.right.right.right
  have targetReadback := SOneComponentClassifier_public_readback classifier
  exact And.intro sourceReadback (And.intro ledgerDeterminacy targetReadback)

end BEDC.Derived.S1Up
