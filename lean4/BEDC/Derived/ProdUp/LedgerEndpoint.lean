import BEDC.Derived.ProdUp

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist

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

end BEDC.Derived.ProdUp
