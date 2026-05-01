import BEDC.Derived.ProdUp

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist

inductive ProdHistoryLedgerChain (Left Right : BHist -> Prop) : BHist -> BHist -> Prop where
  | step {rho z : BHist} :
      ProdHistoryLedgerPolicy Left Right rho z ->
        ProdHistoryLedgerChain Left Right rho z
  | cons {rho v z : BHist} :
      ProdHistoryLedgerPolicy Left Right rho v ->
        ProdHistoryLedgerChain Left Right v z ->
          ProdHistoryLedgerChain Left Right rho z

theorem ProdHistoryLedgerChain_trans {Left Right : BEDC.FKernel.Hist.BHist → Prop}
    {rho mid z : BEDC.FKernel.Hist.BHist} :
    BEDC.Derived.ProdUp.ProdHistoryLedgerChain Left Right rho mid →
      BEDC.Derived.ProdUp.ProdHistoryLedgerChain Left Right mid z →
        BEDC.Derived.ProdUp.ProdHistoryLedgerChain Left Right rho z := by
  intro first
  induction first generalizing z with
  | step ledger =>
      intro second
      exact BEDC.Derived.ProdUp.ProdHistoryLedgerChain.cons ledger second
  | cons ledger _ ih =>
      intro second
      exact BEDC.Derived.ProdUp.ProdHistoryLedgerChain.cons ledger (ih second)

theorem ProdHistoryLedgerPolicy_classifier_endpoint_equivalence {Left Right : BHist → Prop}
    {rho v w : BHist} :
    ProdHistoryLedgerPolicy Left Right rho v →
      (ProdHistoryClassifier Left Right rho w ↔ ProdHistoryClassifier Left Right v w) := by
  intro ledger
  constructor
  · intro rawTarget
    exact ProdHistoryClassifier_trans
      (ProdHistoryClassifier_symm (ProdHistoryLedgerPolicy_raw_visible_classifier ledger))
      rawTarget
  · intro visibleTarget
    exact ProdHistoryLedgerPolicy_classifier_extension ledger visibleTarget

theorem ProdHistoryLedgerPolicy_two_step_classifier_endpoint_equivalence
    {Left Right : BHist -> Prop} {rho v w z : BHist} :
    ProdHistoryLedgerPolicy Left Right rho v ->
      ProdHistoryLedgerPolicy Left Right v w ->
        (ProdHistoryClassifier Left Right rho z <-> ProdHistoryClassifier Left Right w z) := by
  intro firstLedger secondLedger
  have rhoW : ProdHistoryClassifier Left Right rho w :=
    ProdHistoryLedgerPolicy_two_step_classifier_composition firstLedger secondLedger
  constructor
  · intro rhoZ
    exact ProdHistoryClassifier_trans (ProdHistoryClassifier_symm rhoW) rhoZ
  · intro wZ
    exact ProdHistoryClassifier_trans rhoW wZ

theorem ProdHistoryLedgerChain_envelope_closure {Left Right : BHist -> Prop} {rho z : BHist} :
    ProdHistoryLedgerChain Left Right rho z ->
      ProdHistoryCarrier Left Right z /\
        ProdHistoryClassifier Left Right rho z /\
          (forall w : BHist,
            (ProdHistoryClassifier Left Right rho w <->
              ProdHistoryClassifier Left Right z w) /\
              (ProdHistoryClassifier Left Right w rho <->
                ProdHistoryClassifier Left Right w z)) := by
  intro chain
  induction chain with
  | step ledger =>
      have rhoZ :=
        ProdHistoryLedgerPolicy_raw_visible_classifier ledger
      constructor
      · exact ProdHistoryLedgerPolicy_visible_carrier ledger
      · constructor
        · exact rhoZ
        · intro w
          have endpoint :=
            ProdHistoryLedgerPolicy_classifier_endpoint_equivalence (w := w) ledger
          constructor
          · exact endpoint
          · constructor
            · intro wRho
              exact ProdHistoryClassifier_trans wRho rhoZ
            · intro wZ
              exact ProdHistoryClassifier_trans wZ (ProdHistoryClassifier_symm rhoZ)
  | cons ledger _ ih =>
      cases ih with
      | intro carrierZ rest =>
          cases rest with
          | intro vZ endpointZ =>
              have rhoV :=
                ProdHistoryLedgerPolicy_raw_visible_classifier ledger
              have rhoZ :=
                ProdHistoryClassifier_trans rhoV vZ
              constructor
              · exact carrierZ
              · constructor
                · exact rhoZ
                · intro w
                  have endpointV :=
                    ProdHistoryLedgerPolicy_classifier_endpoint_equivalence (w := w) ledger
                  have tailEndpoint := endpointZ w
                  cases tailEndpoint with
                  | intro tailLeft tailRight =>
                      constructor
                      · constructor
                        · intro rhoW
                          exact Iff.mp tailLeft (Iff.mp endpointV rhoW)
                        · intro zW
                          exact Iff.mpr endpointV (Iff.mpr tailLeft zW)
                      · constructor
                        · intro wRho
                          exact ProdHistoryClassifier_trans wRho rhoZ
                        · intro wZ
                          exact ProdHistoryClassifier_trans wZ (ProdHistoryClassifier_symm rhoZ)

end BEDC.Derived.ProdUp
