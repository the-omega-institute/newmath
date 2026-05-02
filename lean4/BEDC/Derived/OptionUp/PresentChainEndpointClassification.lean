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

end BEDC.Derived.OptionUp
