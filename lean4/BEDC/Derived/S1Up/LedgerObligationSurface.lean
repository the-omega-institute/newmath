import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem SOneComponentClassifier_ledger_obligation_surface
    {x y equation point x' y' equation' point' : BHist} :
    SOneHistoryCarrier x y equation point ->
      SOneHistoryCarrier x' y' equation' point' ->
        hsame x x' ->
          hsame y y' ->
            SOneComponentClassifier x y equation point x' y' equation' point' ∧
              Cont x y point ∧ Cont x' y' point' ∧ hsame equation equation' ∧
                hsame point point' := by
  intro leftCarrier rightCarrier sameX sameY
  have ledger :=
    SOneHistoryCarrier_component_classifier_ledger_determinacy leftCarrier rightCarrier
      sameX sameY
  exact And.intro
    (And.intro leftCarrier (And.intro rightCarrier (And.intro sameX sameY)))
    (And.intro leftCarrier.right.right.right
      (And.intro rightCarrier.right.right.right
        (And.intro ledger.left ledger.right)))

end BEDC.Derived.S1Up
