import BEDC.Derived.OptionUp.TaggedPayload

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_visible_pair_payload_exactness {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop}
    (rel_trans : ∀ {x y z : BHist}, Rel x y -> Rel y z -> Rel x z)
    (source_hsame : TaggedOptionSourceHsameCompatible S Rel) {h k a b : BHist} :
    TaggedOptionHistoryClassifier S Rel h k -> S a -> S b ->
      hsame h (BHist.e1 a) -> hsame k (BHist.e1 b) ->
        Rel a b ∧ (hsame h BHist.Empty -> False) ∧
          (hsame k BHist.Empty -> False) ∧
            (∀ a' b' : BHist, S a' -> S b' -> hsame h (BHist.e1 a') ->
              hsame k (BHist.e1 b') -> hsame a a' ∧ hsame b b') := by
  intro classifier sourceA sourceB sameHPresent sameKPresent
  have relAB : Rel a b :=
    TaggedOptionHistoryClassifier_presented_payload_exactness (S := S) (Rel := Rel)
      rel_trans source_hsame classifier sourceA sourceB sameHPresent sameKPresent
  have hNotEmpty : hsame h BHist.Empty -> False := by
    intro sameHEmpty
    exact not_hsame_emp_e1 (hsame_trans (hsame_symm sameHEmpty) sameHPresent)
  have kNotEmpty : hsame k BHist.Empty -> False := by
    intro sameKEmpty
    exact not_hsame_emp_e1 (hsame_trans (hsame_symm sameKEmpty) sameKPresent)
  have payloadUnique :
      ∀ a' b' : BHist, S a' -> S b' -> hsame h (BHist.e1 a') ->
        hsame k (BHist.e1 b') -> hsame a a' ∧ hsame b b' := by
    intro a' b' _sourceA' _sourceB' sameHPresent' sameKPresent'
    exact And.intro
      (hsame_e1_iff.mp (hsame_trans (hsame_symm sameHPresent) sameHPresent'))
      (hsame_e1_iff.mp (hsame_trans (hsame_symm sameKPresent) sameKPresent'))
  exact And.intro relAB (And.intro hNotEmpty (And.intro kNotEmpty payloadUnique))

end BEDC.Derived.OptionUp
