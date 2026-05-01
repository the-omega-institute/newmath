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

end BEDC.Derived.ProdUp
