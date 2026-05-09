import BEDC.Derived.S1Up

namespace BEDC.Derived.S1Up

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SOne_public_namecert_obligation_assembly {x y e p : BHist} :
    SOneHistoryCarrier x y e p ->
      SOneSourceSpec x y e p ∧
        SemanticNameCert
          (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
          (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
          (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
          hsame ∧
        (forall {x' y' e' p' : BHist},
          SOneComponentClassifier x y e p x' y' e' p' ->
            SOneLedgerPolicy x y e p x' y' e' p' ∧
              SOneHistoryCarrier x' y' e' p' ∧ SOneProductHistoryCarrier p' ∧
                hsame e' SOneUnitHistory) := by
  intro carrier
  have sourceSpec : SOneSourceSpec x y e p :=
    SOneSourceSpec_history_carrier_fields carrier
  have cert :
      SemanticNameCert
          (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
          (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
          (fun point : BHist => exists x y e : BHist, SOneHistoryCarrier x y e point)
          hsame :=
    sone_history_semantic_name_certificate carrier
  have classifierRows :
      forall {x' y' e' p' : BHist},
        SOneComponentClassifier x y e p x' y' e' p' ->
          SOneLedgerPolicy x y e p x' y' e' p' ∧
            SOneHistoryCarrier x' y' e' p' ∧ SOneProductHistoryCarrier p' ∧
              hsame e' SOneUnitHistory := by
    intro x' y' e' p' classified
    have ledgerPolicy : SOneLedgerPolicy x y e p x' y' e' p' :=
      SOneLedgerPolicy_component_readback classified
    have targetReadback := SOneHistoryCarrier_public_readback classified.right.left
    exact And.intro ledgerPolicy
      (And.intro classified.right.left
        (And.intro targetReadback.left targetReadback.right.left))
  exact And.intro sourceSpec (And.intro cert classifierRows)

end BEDC.Derived.S1Up
