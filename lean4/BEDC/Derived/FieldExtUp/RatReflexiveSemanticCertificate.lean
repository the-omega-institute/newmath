import BEDC.Derived.FieldExtUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.RatUp

theorem FieldExtRatReflexive_semantic_name_certificate :
    SemanticNameCert RatHistoryCarrier
      (fun h : BHist => RatHistoryCarrier h ∧ RatHistoryCarrier (FieldExtSingletonEmbedding h))
      (fun h : BHist => RatHistoryLedgerPolicy h (FieldExtSingletonEmbedding h))
      RatHistoryClassifier := by
  have ratCert :
      SemanticNameCert RatHistoryCarrier RatHistoryCarrier RatHistoryCarrier
        RatHistoryClassifier :=
    rat_history_semantic_name_certificate
  exact {
    core := ratCert.core
    pattern_sound := by
      intro h carrier
      exact And.intro carrier
        (RatHistoryCarrier_hsame_transport (hsame_symm (append_empty_left h)) carrier)
    ledger_sound := by
      intro h carrier
      exact And.intro carrier (hsame_symm (append_empty_left h))
  }

end BEDC.Derived.FieldExtUp
