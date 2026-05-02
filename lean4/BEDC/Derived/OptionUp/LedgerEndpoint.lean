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

theorem OptionHistoryLedgerPolicy_shared_visible_raw_classifier {source : BHist -> Prop}
    (source_transport : forall {h k : BHist}, hsame h k -> source h -> source k)
    {raw raw' visible : BHist} :
    OptionHistoryLedgerPolicy source raw visible ->
      OptionHistoryLedgerPolicy source raw' visible ->
        OptionHistoryClassifier source raw raw' := by
  intro leftLedger rightLedger
  have leftRawVisible : OptionHistoryClassifier source raw visible :=
    OptionHistoryLedgerPolicy_raw_visible_classifier source_transport leftLedger
  have rightRawVisible : OptionHistoryClassifier source raw' visible :=
    OptionHistoryLedgerPolicy_raw_visible_classifier source_transport rightLedger
  exact OptionHistoryClassifier_trans leftRawVisible (OptionHistoryClassifier_symm rightRawVisible)

theorem OptionHistoryLedgerPolicy_shared_raw_visible_classifier {source : BHist -> Prop}
    (source_transport : forall {h k : BHist}, hsame h k -> source h -> source k)
    {raw visible visible' : BHist} :
    OptionHistoryLedgerPolicy source raw visible ->
      OptionHistoryLedgerPolicy source raw visible' ->
        OptionHistoryClassifier source visible visible' := by
  intro leftLedger rightLedger
  exact OptionHistoryClassifier_trans
    (OptionHistoryClassifier_symm
      (OptionHistoryLedgerPolicy_raw_visible_classifier source_transport leftLedger))
    (OptionHistoryLedgerPolicy_raw_visible_classifier source_transport rightLedger)

theorem OptionHistoryLedgerPolicy_trans {source : BHist -> Prop} {raw mid visible : BHist} :
    OptionHistoryLedgerPolicy source raw mid ->
      OptionHistoryLedgerPolicy source mid visible ->
        OptionHistoryLedgerPolicy source raw visible := by
  intro first second
  cases first with
  | intro rawCarrier rawMid =>
      cases second with
      | intro _midCarrier midVisible =>
          exact And.intro rawCarrier (hsame_trans rawMid midVisible)

theorem OptionHistoryLedgerPolicy_source_monotonicity {S T : BHist -> Prop}
    (source_mono : forall {h : BHist}, S h -> T h) {raw visible : BHist} :
    OptionHistoryLedgerPolicy S raw visible -> OptionHistoryLedgerPolicy T raw visible := by
  intro ledger
  cases ledger with
  | intro rawCarrier rawVisible =>
      constructor
      · cases rawCarrier with
        | inl rawEmpty =>
            exact Or.inl rawEmpty
        | inr rawSource =>
            exact Or.inr (source_mono rawSource)
      · exact rawVisible

end BEDC.Derived.OptionUp
