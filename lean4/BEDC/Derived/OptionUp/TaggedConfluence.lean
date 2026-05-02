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

theorem TaggedOptionHistoryClassifier_common_right_visible_payload_classification
    {S : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    (rel_symm : forall {x y : BHist}, Rel x y -> Rel y x)
    (rel_trans : forall {x y z : BHist}, Rel x y -> Rel y z -> Rel x z)
    (source_hsame : forall {x y : BHist}, S x -> S y -> hsame x y -> Rel x y)
    {h r k a c b : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      TaggedOptionHistoryClassifier S Rel r k ->
        S a -> S c -> S b -> hsame h (BHist.e1 a) -> hsame r (BHist.e1 c) ->
          hsame k (BHist.e1 b) -> Rel a c := by
  intro left right sourceA sourceC sourceB sameHA sameRC sameKB
  have leftVisible := TaggedOptionHistoryClassifier_right_visible_branch_inversion left
  have rightVisible := TaggedOptionHistoryClassifier_right_visible_branch_inversion right
  have leftData := leftVisible.right sourceB sameKB
  have rightData := rightVisible.right sourceB sameKB
  cases leftData with
  | intro leftPayload leftRest =>
      cases leftRest with
      | intro leftTarget leftFields =>
          cases leftFields with
          | intro sourceLeftPayload leftFields =>
              cases leftFields with
              | intro sourceLeftTarget leftFields =>
                  cases leftFields with
                  | intro sameBLeftTarget leftFields =>
                      cases leftFields with
                      | intro relLeft leftEndpoint =>
                          have sameALeftPayload : hsame a leftPayload :=
                            hsame_e1_iff.mp (hsame_trans (hsame_symm sameHA) leftEndpoint)
                          have relALeftPayload : Rel a leftPayload :=
                            source_hsame sourceA sourceLeftPayload sameALeftPayload
                          have relLeftTargetB : Rel leftTarget b :=
                            source_hsame sourceLeftTarget sourceB (hsame_symm sameBLeftTarget)
                          have relAB : Rel a b :=
                            rel_trans (rel_trans relALeftPayload relLeft) relLeftTargetB
                          cases rightData with
                          | intro rightPayload rightRest =>
                              cases rightRest with
                              | intro rightTarget rightFields =>
                                  cases rightFields with
                                  | intro sourceRightPayload rightFields =>
                                      cases rightFields with
                                      | intro sourceRightTarget rightFields =>
                                          cases rightFields with
                                          | intro sameBRightTarget rightFields =>
                                              cases rightFields with
                                              | intro relRight rightEndpoint =>
                                                  have sameCRightPayload :
                                                      hsame c rightPayload :=
                                                    hsame_e1_iff.mp
                                                      (hsame_trans (hsame_symm sameRC)
                                                        rightEndpoint)
                                                  have relCRightPayload : Rel c rightPayload :=
                                                    source_hsame sourceC sourceRightPayload
                                                      sameCRightPayload
                                                  have relRightTargetB : Rel rightTarget b :=
                                                    source_hsame sourceRightTarget sourceB
                                                      (hsame_symm sameBRightTarget)
                                                  have relCB : Rel c b :=
                                                    rel_trans
                                                      (rel_trans relCRightPayload relRight)
                                                      relRightTargetB
                                                  exact rel_trans relAB (rel_symm relCB)

theorem TaggedOptionHistoryClassifier_common_left_visible_payload_classification
    {S : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    (rel_symm : forall {x y : BHist}, Rel x y -> Rel y x)
    (rel_trans : forall {x y z : BHist}, Rel x y -> Rel y z -> Rel x z)
    (source_hsame : forall {x y : BHist}, S x -> S y -> hsame x y -> Rel x y)
    {h k r a b c : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      TaggedOptionHistoryClassifier S Rel h r ->
        S a -> S b -> S c -> hsame h (BHist.e1 a) -> hsame k (BHist.e1 b) ->
          hsame r (BHist.e1 c) -> Rel b c := by
  intro left right sourceA sourceB sourceC sameHA sameKB sameRC
  cases left with
  | inl absentLeft =>
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm absentLeft.left) sameHA))
  | inr presentLeft =>
      cases presentLeft with
      | intro leftSourcePayload leftRest =>
          cases leftRest with
          | intro leftTargetPayload leftData =>
              cases leftData with
              | intro sourceLeftSource leftData =>
                  cases leftData with
                  | intro sourceLeftTarget leftData =>
                      cases leftData with
                      | intro sameLeftSource leftData =>
                          cases leftData with
                          | intro sameLeftTarget relLeft =>
                              have sameALeftSource : hsame a leftSourcePayload :=
                                hsame_e1_iff.mp
                                  (hsame_trans (hsame_symm sameHA) sameLeftSource)
                              have sameBLeftTarget : hsame b leftTargetPayload :=
                                hsame_e1_iff.mp
                                  (hsame_trans (hsame_symm sameKB) sameLeftTarget)
                              have relBLeftTarget : Rel b leftTargetPayload :=
                                source_hsame sourceB sourceLeftTarget sameBLeftTarget
                              have relLeftSourceA : Rel leftSourcePayload a :=
                                source_hsame sourceLeftSource sourceA (hsame_symm sameALeftSource)
                              have relBA : Rel b a :=
                                rel_trans
                                  (rel_trans relBLeftTarget (rel_symm relLeft))
                                  relLeftSourceA
                              cases right with
                              | inl absentRight =>
                                  exact False.elim
                                    (not_hsame_emp_e1
                                      (hsame_trans (hsame_symm absentRight.left) sameHA))
                              | inr presentRight =>
                                  cases presentRight with
                                  | intro rightSourcePayload rightRest =>
                                      cases rightRest with
                                      | intro rightTargetPayload rightData =>
                                          cases rightData with
                                          | intro sourceRightSource rightData =>
                                              cases rightData with
                                              | intro sourceRightTarget rightData =>
                                                  cases rightData with
                                                  | intro sameRightSource rightData =>
                                                      cases rightData with
                                                      | intro sameRightTarget relRight =>
                                                          have sameARightSource :
                                                              hsame a rightSourcePayload :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans (hsame_symm sameHA)
                                                                sameRightSource)
                                                          have sameCRightTarget :
                                                              hsame c rightTargetPayload :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans (hsame_symm sameRC)
                                                                sameRightTarget)
                                                          have relARightSource :
                                                              Rel a rightSourcePayload :=
                                                            source_hsame sourceA
                                                              sourceRightSource
                                                              sameARightSource
                                                          have relRightTargetC :
                                                              Rel rightTargetPayload c :=
                                                            source_hsame sourceRightTarget
                                                              sourceC
                                                              (hsame_symm sameCRightTarget)
                                                          have relAC : Rel a c :=
                                                            rel_trans
                                                              (rel_trans relARightSource relRight)
                                                              relRightTargetC
                                                          exact rel_trans relBA relAC

end BEDC.Derived.OptionUp
