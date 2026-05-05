import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp

theorem SOneHistoryCarrier_semanticNameCert_field_assembly {x y e p : BHist} :
    SOneHistoryCarrier x y e p ->
      (SOneProductHistoryCarrier p ∧ hsame e SOneUnitHistory ∧
        exists dx dy : BHist,
          hsame x (BHist.e1 dx) ∧ RatHistoryCarrier dx ∧
            hsame y (BHist.e1 dy) ∧ RatHistoryCarrier dy ∧ Cont x y p) ∧
      (forall {x' y' e' p' : BHist},
        SOneComponentClassifier x y e p x' y' e' p' -> hsame e e' ∧ hsame p p') ∧
      (forall {x' y' e' p' : BHist},
        SOneComponentClassifier x y e p x' y' e' p' ->
          SOneHistoryCarrier x' y' e' p') ∧
      SemanticNameCert
        (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
        (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
        (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
        hsame := by
  intro carrier
  have readback := SOneHistoryCarrier_public_readback carrier
  have ledgerDeterminacy :
      forall {x' y' e' p' : BHist},
        SOneComponentClassifier x y e p x' y' e' p' -> hsame e e' ∧ hsame p p' := by
    intro x' y' e' p' classified
    exact SOneComponentClassifier_stability.right.right.right.left classified
  have carrierTransport :
      forall {x' y' e' p' : BHist},
        SOneComponentClassifier x y e p x' y' e' p' ->
          SOneHistoryCarrier x' y' e' p' := by
    intro x' y' e' p' classified
    exact SOneComponentClassifier_stability.right.right.right.right classified
  exact And.intro readback
    (And.intro ledgerDeterminacy
      (And.intro carrierTransport (sone_history_semantic_name_certificate carrier)))

end BEDC.Derived.S1Up
