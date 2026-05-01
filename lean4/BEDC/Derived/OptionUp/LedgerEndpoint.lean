import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem OptionHistoryLedgerPolicy_classifier_endpoint_equivalence {source : BHist -> Prop}
    (source_transport : forall {h k : BHist}, hsame h k -> source h -> source k)
    {raw visible target : BHist} :
    OptionHistoryLedgerPolicy source raw visible ->
      (OptionHistoryClassifier source raw target <->
        OptionHistoryClassifier source visible target) := by
  intro ledger
  have rawVisible : OptionHistoryClassifier source raw visible :=
    OptionHistoryLedgerPolicy_raw_visible_classifier source_transport ledger
  constructor
  · intro rawTarget
    exact OptionHistoryClassifier_trans (OptionHistoryClassifier_symm rawVisible) rawTarget
  · intro visibleTarget
    exact OptionHistoryLedgerPolicy_classifier_extension source_transport ledger visibleTarget

end BEDC.Derived.OptionUp
