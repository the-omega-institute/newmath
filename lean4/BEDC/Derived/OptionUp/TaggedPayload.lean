import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

def TaggedOptionSourceHsameCompatible (S : BHist → Prop) (Rel : BHist → BHist → Prop) :
    Prop :=
  ∀ {a b : BHist}, S a → S b → hsame a b → Rel a b

theorem TaggedOptionHistoryClassifier_presented_payload_exactness {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop}
    (rel_trans : forall {x y z : BHist}, Rel x y -> Rel y z -> Rel x z)
    (source_hsame : forall {x y : BHist}, S x -> S y -> hsame x y -> Rel x y)
    {h k a b : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      S a ->
        S b ->
          hsame h (BHist.e1 a) ->
            hsame k (BHist.e1 b) ->
              Rel a b := by
  intro classifier sourceA sourceB sameHPresentA sameKPresentB
  cases classifier with
  | inl absentPair =>
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm absentPair.left) sameHPresentA))
  | inr presentPair =>
      cases presentPair with
      | intro a0 restA =>
          cases restA with
          | intro b0 data =>
              cases data with
              | intro sourceA0 rest =>
                  cases rest with
                  | intro sourceB0 rest =>
                      cases rest with
                      | intro sameHPresentA0 rest =>
                          cases rest with
                          | intro sameKPresentB0 relA0B0 =>
                              have sameAA0 : hsame a a0 :=
                                hsame_e1_iff.mp
                                  (hsame_trans (hsame_symm sameHPresentA) sameHPresentA0)
                              have sameB0B : hsame b0 b :=
                                hsame_e1_iff.mp
                                  (hsame_trans (hsame_symm sameKPresentB0) sameKPresentB)
                              have relAA0 : Rel a a0 :=
                                source_hsame sourceA sourceA0 sameAA0
                              have relB0B : Rel b0 b :=
                                source_hsame sourceB0 sourceB sameB0B
                              exact rel_trans (rel_trans relAA0 relA0B0) relB0B

theorem TaggedOptionHistoryClassifier_visible_present_exactness {S : BHist → Prop}
    {Rel : BHist → BHist → Prop}
    (rel_trans : ∀ {x y z : BHist}, Rel x y → Rel y z → Rel x z)
    (source_hsame : TaggedOptionSourceHsameCompatible S Rel) {h k : BHist} :
    S h → S k →
      (TaggedOptionHistoryClassifier S Rel (BHist.e1 h) (BHist.e1 k) ↔ Rel h k) := by
  intro sourceH sourceK
  constructor
  · intro classifier
    exact TaggedOptionHistoryClassifier_presented_payload_exactness (S := S) (Rel := Rel)
      rel_trans source_hsame classifier sourceH sourceK (hsame_refl (BHist.e1 h))
      (hsame_refl (BHist.e1 k))
  · intro relHK
    exact Or.inr
      (Exists.intro h
        (Exists.intro k
          (And.intro sourceH
            (And.intro sourceK
              (And.intro (hsame_refl (BHist.e1 h))
                (And.intro (hsame_refl (BHist.e1 k)) relHK))))))

end BEDC.Derived.OptionUp
