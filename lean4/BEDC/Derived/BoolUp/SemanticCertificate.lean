import BEDC.Derived.BoolUp

namespace BEDC.Derived.BoolUp

theorem bool_history_semantic_name_certificate :
    BEDC.FKernel.NameCert.SemanticNameCert BoolHistoryCarrier BoolHistoryCarrier
      BoolHistoryCarrier BoolHistoryClassifier := by
  exact {
    core := bool_history_name_certificate
    pattern_sound := by
      intro h carrier
      exact carrier
    ledger_sound := by
      intro h carrier
      exact carrier
  }

end BEDC.Derived.BoolUp
