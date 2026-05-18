import BEDC.Derived.SumUp.Classifier

namespace BEDC.Derived.SumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem SumUp_concrete_to_schema {Left Right : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop}
    (leftCert : NameCert Left LeftEq) (rightCert : NameCert Right RightEq) :
    SemanticNameCert (SumHistoryCarrier Left Right) (SumHistoryCarrier Left Right)
        (SumHistoryCarrier Left Right) (SumHistoryClassifier Left Right LeftEq RightEq) ∧
      (∀ {l r : BHist},
        SumHistoryClassifier Left Right LeftEq RightEq (BHist.e0 l) (BHist.e1 r) →
          False) ∧
      (∀ {l l' : BHist},
        SumHistoryClassifier Left Right hsame hsame (BHist.e0 l) (BHist.e0 l') →
          hsame l l') ∧
      (∀ {r r' : BHist},
        SumHistoryClassifier Left Right hsame hsame (BHist.e1 r) (BHist.e1 r') →
          hsame r r') := by
  -- BEDC touchpoint anchor: BHist hsame NameCert SemanticNameCert
  constructor
  · exact sum_history_semantic_name_certificate leftCert rightCert
  · constructor
    · intro l r classifier
      exact SumHistoryClassifier_mixed_tags_absurd
        (Left := Left) (Right := Right) (LeftEq := LeftEq) (RightEq := RightEq)
        (hsame_refl (BHist.e0 l)) (hsame_refl (BHist.e1 r)) classifier
    · constructor
      · intro l l' classifier
        exact SumHistoryClassifier_left_hsame_inversion classifier
      · intro r r' classifier
        exact SumHistoryClassifier_right_hsame_inversion classifier

end BEDC.Derived.SumUp
