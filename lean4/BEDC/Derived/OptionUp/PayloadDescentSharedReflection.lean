import BEDC.Derived.OptionUp.PayloadDescentImageClassifier

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionMapRel_shared_target_source_reflection_normal_form
    {S T : BHist -> Prop} {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (reflects : TaggedOptionPayloadDescentReflectsSource S delta) {h h' k : BHist} :
    TaggedOptionMapRel S T delta h k ->
      TaggedOptionMapRel S T delta h' k ->
        (hsame h BHist.Empty ∧ hsame h' BHist.Empty ∧ hsame k BHist.Empty) ∨
          (∃ a : BHist, ∃ b : BHist,
            S a ∧ S b ∧ RelS a b ∧ T (delta.map a) ∧ T (delta.map b) ∧
              hsame h (BHist.e1 a) ∧ hsame h' (BHist.e1 b) ∧
                hsame k (BHist.e1 (delta.map a)) ∧
                  hsame k (BHist.e1 (delta.map b)) ∧
                    TaggedOptionHistoryClassifier S RelS h h') := by
  intro left right
  cases left with
  | inl absentLeft =>
      cases right with
      | inl absentRight =>
          exact Or.inl (And.intro absentLeft.left
            (And.intro absentRight.left absentLeft.right))
      | inr presentRight =>
          cases presentRight with
          | intro _b dataRight =>
              exact False.elim
                (not_hsame_emp_e1
                  (hsame_trans (hsame_symm absentLeft.right) dataRight.right.right.right))
  | inr presentLeft =>
      cases presentLeft with
      | intro a dataLeft =>
          cases right with
          | inl absentRight =>
              exact False.elim
                (not_hsame_e1_empty
                  (hsame_trans (hsame_symm dataLeft.right.right.right) absentRight.right))
          | inr presentRight =>
              cases presentRight with
              | intro b dataRight =>
                  have sameTarget : hsame (delta.map a) (delta.map b) :=
                    hsame_e1_iff.mp
                      (hsame_trans (hsame_symm dataLeft.right.right.right)
                        dataRight.right.right.right)
                  have relAB : RelS a b :=
                    reflects a b dataLeft.left dataRight.left sameTarget
                  have sourceClass : TaggedOptionHistoryClassifier S RelS h h' :=
                    Or.inr
                      (Exists.intro a
                        (Exists.intro b
                          (And.intro dataLeft.left
                            (And.intro dataRight.left
                              (And.intro dataLeft.right.right.left
                                (And.intro dataRight.right.right.left relAB))))))
                  exact Or.inr
                    (Exists.intro a
                      (Exists.intro b
                        (And.intro dataLeft.left
                          (And.intro dataRight.left
                            (And.intro relAB
                              (And.intro dataLeft.right.left
                                (And.intro dataRight.right.left
                                  (And.intro dataLeft.right.right.left
                                    (And.intro dataRight.right.right.left
                                      (And.intro dataLeft.right.right.right
                                        (And.intro dataRight.right.right.right
                                          sourceClass)))))))))))

end BEDC.Derived.OptionUp
