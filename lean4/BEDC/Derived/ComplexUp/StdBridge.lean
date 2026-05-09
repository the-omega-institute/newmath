import BEDC.Derived.ComplexUp

namespace BEDC.Derived.ComplexUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ComplexUp_StdBridge :
    SemanticNameCert ComplexHistoryCarrier ComplexHistoryCarrier ComplexHistoryCarrier
        ComplexHistoryClassifier ∧
      (∀ {raw visible : BHist},
        ComplexHistoryLedgerPolicy raw visible -> ComplexHistoryClassifier raw visible) := by
  exact And.intro complex_history_semantic_name_certificate
    (fun {raw visible} ledger => ComplexHistoryLedgerPolicy_raw_visible_classifier ledger)

end BEDC.Derived.ComplexUp
