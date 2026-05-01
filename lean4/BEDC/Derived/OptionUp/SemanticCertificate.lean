import BEDC.Derived.OptionUp.StabilityFields

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionHistoryCarrier_semanticNameCert {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert S Rel) :
    SemanticNameCert (TaggedOptionHistoryCarrier S) (TaggedOptionHistoryCarrier S)
      (TaggedOptionHistoryCarrier S) (TaggedOptionHistoryClassifier S Rel) := by
  have fields := TaggedOptionHistoryClassifier_stability_fields (S := S) (Rel := Rel) cert
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro BHist.Empty (Or.inl (hsame_refl BHist.Empty))
      equiv_refl := fields.left
      equiv_symm := fields.right.left
      equiv_trans := fields.right.right.left
      carrier_respects_equiv := by
        intro h k same carrier
        exact fields.right.right.right.left carrier same
    }
    pattern_sound := by
      intro h carrier
      exact carrier
    ledger_sound := by
      intro h carrier
      exact carrier
  }

end BEDC.Derived.OptionUp
