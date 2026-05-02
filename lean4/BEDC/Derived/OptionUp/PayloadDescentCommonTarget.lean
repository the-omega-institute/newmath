import BEDC.Derived.OptionUp.PayloadDescentImageClassifier

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionMapRel_common_target_source_classification {S T : BHist -> Prop}
    {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (reflects : TaggedOptionPayloadDescentReflectsSource S delta) {h h' k : BHist} :
    TaggedOptionMapRel S T delta h k ->
      TaggedOptionMapRel S T delta h' k ->
        TaggedOptionHistoryClassifier S RelS h h' := by
  intro left right
  cases left with
  | inl leftAbsent =>
      cases right with
      | inl rightAbsent =>
          exact Or.inl (And.intro leftAbsent.left rightAbsent.left)
      | inr rightPresent =>
          cases rightPresent with
          | intro b rightData =>
              exact False.elim
                (not_hsame_emp_e1
                  (hsame_trans (hsame_symm leftAbsent.right) rightData.right.right.right))
  | inr leftPresent =>
      cases leftPresent with
      | intro a leftData =>
          cases right with
          | inl rightAbsent =>
              exact False.elim
                (not_hsame_emp_e1
                  (hsame_trans (hsame_symm rightAbsent.right) leftData.right.right.right))
          | inr rightPresent =>
              cases rightPresent with
              | intro b rightData =>
                  have samePayload : hsame (delta.map a) (delta.map b) :=
                    hsame_e1_iff.mp
                      (hsame_trans (hsame_symm leftData.right.right.right)
                        rightData.right.right.right)
                  exact Or.inr
                    (Exists.intro a
                      (Exists.intro b
                        (And.intro leftData.left
                          (And.intro rightData.left
                            (And.intro leftData.right.right.left
                              (And.intro rightData.right.right.left
                                (reflects a b leftData.left rightData.left samePayload)))))))

end BEDC.Derived.OptionUp
