import BEDC.Derived.OptionUp.StabilityFields

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionHistoryClassifier_present_chain_endpoint_classification {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert S Rel) {h k r a c : BHist} :
    TaggedOptionHistoryClassifier S Rel h k -> TaggedOptionHistoryClassifier S Rel k r ->
      hsame h (BHist.e1 a) -> hsame r (BHist.e1 c) ->
        exists a0 c0 : BHist,
          S a0 /\ S c0 /\ hsame a a0 /\ hsame c0 c /\ Rel a0 c0 := by
  intro classifiedHK classifiedKR sameH sameR
  have classifiedHR : TaggedOptionHistoryClassifier S Rel h r :=
    TaggedOptionHistoryClassifier_trans
      (S := S) (Rel := Rel)
      (fun {a b c} relAB relBC => NameCert.equiv_trans cert relAB relBC)
      classifiedHK classifiedKR
  cases classifiedHR with
  | inl absent =>
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameH))
  | inr present =>
      cases present with
      | intro a0 restA =>
          cases restA with
          | intro c0 data =>
              cases data with
              | intro sourceA0 rest =>
                  cases rest with
                  | intro sourceC0 rest =>
                      cases rest with
                      | intro sameHPresent rest =>
                          cases rest with
                          | intro sameRPresent relA0C0 =>
                              have sameAA0 : hsame a a0 :=
                                hsame_e1_iff.mp
                                  (hsame_trans (hsame_symm sameH) sameHPresent)
                              have sameC0C : hsame c0 c :=
                                hsame_e1_iff.mp
                                  (hsame_trans (hsame_symm sameRPresent) sameR)
                              exact Exists.intro a0
                                (Exists.intro c0
                                  (And.intro sourceA0
                                  (And.intro sourceC0
                                      (And.intro sameAA0
                                        (And.intro sameC0C relA0C0)))))

theorem TaggedOptionHistoryClassifier_present_chain_visible_endpoint_classification
    {S : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    (rel_trans : forall {a b c : BHist}, Rel a b -> Rel b c -> Rel a c)
    (source_hsame : forall {a b : BHist}, S a -> S b -> hsame a b -> Rel a b)
    {h k r a c : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      TaggedOptionHistoryClassifier S Rel k r ->
        S a -> S c -> hsame h (BHist.e1 a) -> hsame r (BHist.e1 c) -> Rel a c := by
  intro classifiedHK classifiedKR sourceA sourceC sameH sameR
  have classifiedHR : TaggedOptionHistoryClassifier S Rel h r :=
    TaggedOptionHistoryClassifier_trans
      (S := S) (Rel := Rel) rel_trans classifiedHK classifiedKR
  cases classifiedHR with
  | inl absent =>
      exact False.elim
        (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameH))
  | inr present =>
      cases present with
      | intro left restLeft =>
          cases restLeft with
          | intro right data =>
              cases data with
              | intro sourceLeft rest =>
                  cases rest with
                  | intro sourceRight rest =>
                      cases rest with
                      | intro sameHPresent rest =>
                          cases rest with
                          | intro sameRPresent relLeftRight =>
                              have sameALeft : hsame a left :=
                                hsame_e1_iff.mp
                                  (hsame_trans (hsame_symm sameH) sameHPresent)
                              have sameRightC : hsame right c :=
                                hsame_e1_iff.mp
                                  (hsame_trans (hsame_symm sameRPresent) sameR)
                              exact rel_trans
                                (source_hsame sourceA sourceLeft sameALeft)
                                (rel_trans relLeftRight
                                  (source_hsame sourceRight sourceC sameRightC))

end BEDC.Derived.OptionUp
