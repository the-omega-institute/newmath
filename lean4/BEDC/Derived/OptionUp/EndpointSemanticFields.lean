import BEDC.Derived.OptionUp.BranchExactness

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionHistoryClassifier_endpoint_semantic_fields {S Pattern Ledger : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop}
    (cert : SemanticNameCert (TaggedOptionHistoryCarrier S) Pattern Ledger
      (TaggedOptionHistoryClassifier S Rel))
    {h k : BHist} :
    TaggedOptionHistoryClassifier S Rel h k -> Pattern h ∧ Ledger h ∧ Pattern k ∧ Ledger k := by
  intro classifier
  have endpointCarriers := TaggedOptionHistoryClassifier_endpoint_carriers classifier
  exact
    And.intro (cert.pattern_sound endpointCarriers.left)
      (And.intro (cert.ledger_sound endpointCarriers.left)
        (And.intro (cert.pattern_sound endpointCarriers.right)
          (cert.ledger_sound endpointCarriers.right)))

end BEDC.Derived.OptionUp
