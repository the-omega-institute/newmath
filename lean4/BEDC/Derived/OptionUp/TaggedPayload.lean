import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

def TaggedOptionSourceHsameCompatible (S : BHist → Prop) (Rel : BHist → BHist → Prop) :
    Prop :=
  ∀ {a b : BHist}, S a → S b → hsame a b → Rel a b

theorem TaggedOptionHistoryClassifier_present_present_exactness {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k : BHist} :
    TaggedOptionHistoryClassifier S Rel (BHist.e1 h) (BHist.e1 k) ↔
      ∃ a : BHist, ∃ b : BHist,
        S a ∧ S b ∧ hsame h a ∧ hsame k b ∧ Rel a b := by
  constructor
  · intro classifier
    cases classifier with
    | inl absentPair =>
        exact False.elim (not_hsame_e1_empty absentPair.left)
    | inr presentPair =>
        cases presentPair with
        | intro a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro sourceA rest =>
                    cases rest with
                    | intro sourceB rest =>
                        cases rest with
                        | intro sameHPresent rest =>
                            cases rest with
                            | intro sameKPresent relAB =>
                                exact Exists.intro a
                                  (Exists.intro b
                                    (And.intro sourceA
                                      (And.intro sourceB
                                        (And.intro (hsame_e1_iff.mp sameHPresent)
                                          (And.intro (hsame_e1_iff.mp sameKPresent)
                                            relAB)))))
  · intro presentPair
    cases presentPair with
    | intro a restA =>
        cases restA with
        | intro b data =>
            cases data with
            | intro sourceA rest =>
                cases rest with
                | intro sourceB rest =>
                    cases rest with
                    | intro sameHA rest =>
                        cases rest with
                        | intro sameKB relAB =>
                            exact Or.inr
                              (Exists.intro a
                                (Exists.intro b
                                  (And.intro sourceA
                                    (And.intro sourceB
                                      (And.intro (hsame_e1_congr sameHA)
                                        (And.intro (hsame_e1_congr sameKB) relAB))))))

theorem TaggedOptionHistoryClassifier_same_tag_exactness {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k : BHist} :
    (TaggedOptionHistoryClassifier S Rel BHist.Empty k ↔ hsame k BHist.Empty) ∧
      (TaggedOptionHistoryClassifier S Rel (BHist.e1 h) (BHist.e1 k) ↔
        ∃ a : BHist, ∃ b : BHist,
          S a ∧ S b ∧ hsame h a ∧ hsame k b ∧ Rel a b) := by
  constructor
  · constructor
    · intro classifier
      cases classifier with
      | inl absentPair =>
          exact absentPair.right
      | inr presentPair =>
          cases presentPair with
          | intro a restA =>
              cases restA with
              | intro _b data =>
                  cases data with
                  | intro _sourceA rest =>
                      cases rest with
                      | intro _sourceB rest =>
                          cases rest with
                          | intro sameEmptyPresent _rest =>
                              exact False.elim (not_hsame_emp_e1 sameEmptyPresent)
    · intro sameKEmpty
      exact Or.inl (And.intro (hsame_refl BHist.Empty) sameKEmpty)
  · exact TaggedOptionHistoryClassifier_present_present_exactness

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

theorem TaggedOptionHistoryClassifier_hsame_present_exactness {S : BHist -> Prop}
    (source_transport : ∀ {x y : BHist}, hsame x y -> S x -> S y) {h k : BHist} :
    TaggedOptionHistoryClassifier S hsame (BHist.e1 h) (BHist.e1 k) ↔
      S h ∧ S k ∧ hsame h k := by
  constructor
  · intro classifier
    have presentPair :
        ∃ a : BHist, ∃ b : BHist,
          S a ∧ S b ∧ hsame h a ∧ hsame k b ∧ hsame a b :=
      TaggedOptionHistoryClassifier_present_present_exactness.mp classifier
    cases presentPair with
    | intro a restA =>
        cases restA with
        | intro b data =>
            cases data with
            | intro sourceA rest =>
                cases rest with
                | intro sourceB rest =>
                    cases rest with
                    | intro sameHA rest =>
                        cases rest with
                        | intro sameKB sameAB =>
                            exact And.intro (source_transport (hsame_symm sameHA) sourceA)
                              (And.intro (source_transport (hsame_symm sameKB) sourceB)
                                (hsame_trans sameHA (hsame_trans sameAB (hsame_symm sameKB))))
  · intro data
    cases data with
    | intro sourceH rest =>
        cases rest with
        | intro sourceK sameHK =>
            exact TaggedOptionHistoryClassifier_present_present_exactness.mpr
              (Exists.intro h
                (Exists.intro k
                  (And.intro sourceH
                    (And.intro sourceK
                      (And.intro (hsame_refl h) (And.intro (hsame_refl k) sameHK))))))

end BEDC.Derived.OptionUp
