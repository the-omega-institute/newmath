import BEDC.Derived.OptionUp

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist

theorem TaggedOptionHistoryClassifier_left_confluence {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop}
    (rel_symm : forall {a b : BHist}, Rel a b -> Rel b a)
    (rel_trans : forall {a b c : BHist}, Rel a b -> Rel b c -> Rel a c)
    {h k r : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      TaggedOptionHistoryClassifier S Rel h r ->
        TaggedOptionHistoryClassifier S Rel k r := by
  intro left right
  have flipped : TaggedOptionHistoryClassifier S Rel k h := by
    cases left with
    | inl absent =>
        exact Or.inl (And.intro absent.right absent.left)
    | inr present =>
        cases present with
        | intro a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro sourceA rest =>
                    cases rest with
                    | intro sourceB rest =>
                        cases rest with
                        | intro sameH rest =>
                            cases rest with
                            | intro sameK relAB =>
                                exact Or.inr
                                  (Exists.intro b
                                    (Exists.intro a
                                      (And.intro sourceB
                                        (And.intro sourceA
                                          (And.intro sameK
                                            (And.intro sameH (rel_symm relAB)))))))
  exact TaggedOptionHistoryClassifier_trans (S := S) (Rel := Rel) rel_trans flipped right

theorem TaggedOptionHistoryClassifier_right_confluence {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop}
    (rel_symm : forall {a b : BHist}, Rel a b -> Rel b a)
    (rel_trans : forall {a b c : BHist}, Rel a b -> Rel b c -> Rel a c)
    {h k r : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      TaggedOptionHistoryClassifier S Rel r k ->
        TaggedOptionHistoryClassifier S Rel h r := by
  intro left right
  have flipped : TaggedOptionHistoryClassifier S Rel k r := by
    cases right with
    | inl absent =>
        exact Or.inl (And.intro absent.right absent.left)
    | inr present =>
        cases present with
        | intro a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro sourceA rest =>
                    cases rest with
                    | intro sourceB rest =>
                        cases rest with
                        | intro sameR rest =>
                            cases rest with
                            | intro sameK relAB =>
                                exact Or.inr
                                  (Exists.intro b
                                    (Exists.intro a
                                      (And.intro sourceB
                                        (And.intro sourceA
                                          (And.intro sameK
                                            (And.intro sameR (rel_symm relAB)))))))
  exact TaggedOptionHistoryClassifier_trans (S := S) (Rel := Rel) rel_trans left flipped

end BEDC.Derived.OptionUp
