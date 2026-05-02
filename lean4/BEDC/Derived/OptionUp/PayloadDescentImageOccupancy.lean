import BEDC.Derived.OptionUp.PayloadDescentImageClassifier

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageClassifier_branch_occupancy_equivalence
    {S T : BHist -> Prop} {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' ->
      (hsame k BHist.Empty <-> hsame k' BHist.Empty) /\
        ((exists a : BHist, S a /\ T (delta.map a) /\ hsame k (BHist.e1 (delta.map a))) <->
          (exists b : BHist, S b /\ T (delta.map b) /\ hsame k' (BHist.e1 (delta.map b)))) := by
  intro image
  have branch :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp
      image
  constructor
  · constructor
    · intro sameLeftEmpty
      cases branch with
      | inl absent =>
          exact absent.right
      | inr present =>
          cases present with
          | intro _a present =>
              cases present with
              | intro _b data =>
                  exact False.elim
                    (not_hsame_emp_e1
                      (hsame_trans (hsame_symm sameLeftEmpty)
                        data.right.right.right.right.right.left))
    · intro sameRightEmpty
      cases branch with
      | inl absent =>
          exact absent.left
      | inr present =>
          cases present with
          | intro _a present =>
              cases present with
              | intro _b data =>
                  exact False.elim
                    (not_hsame_emp_e1
                      (hsame_trans (hsame_symm sameRightEmpty)
                        data.right.right.right.right.right.right))
  · constructor
    · intro leftPresent
      cases branch with
      | inl absent =>
          cases leftPresent with
          | intro _a data =>
              exact False.elim
                (not_hsame_emp_e1
                  (hsame_trans (hsame_symm absent.left) data.right.right))
      | inr present =>
          cases present with
          | intro _a present =>
              cases present with
              | intro b data =>
                  exact Exists.intro b
                    (And.intro data.right.left
                      (And.intro data.right.right.right.right.left
                        data.right.right.right.right.right.right))
    · intro rightPresent
      cases branch with
      | inl absent =>
          cases rightPresent with
          | intro _b data =>
              exact False.elim
                (not_hsame_emp_e1
                  (hsame_trans (hsame_symm absent.right) data.right.right))
      | inr present =>
          cases present with
          | intro a present =>
              cases present with
              | intro _b data =>
                  exact Exists.intro a
                    (And.intro data.left
                      (And.intro data.right.right.right.left
                        data.right.right.right.right.right.left))

end BEDC.Derived.OptionUp
