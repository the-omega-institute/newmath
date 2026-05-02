import BEDC.Derived.OptionUp.PayloadDescentImageClassifier

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionMapRel_shared_target_source_reflection_normal_form
    {S T : BHist → Prop} {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (reflects : TaggedOptionPayloadDescentReflectsSource S delta) {h h' k : BHist} :
    TaggedOptionMapRel S T delta h k →
      TaggedOptionMapRel S T delta h' k →
        (hsame h BHist.Empty ∧ hsame h' BHist.Empty ∧ hsame k BHist.Empty) ∨
          (∃ a b : BHist,
            S a ∧ S b ∧ RelS a b ∧ T (delta.map a) ∧ T (delta.map b) ∧
              hsame h (BHist.e1 a) ∧ hsame h' (BHist.e1 b) ∧
                hsame k (BHist.e1 (delta.map a)) ∧
                  hsame k (BHist.e1 (delta.map b)) ∧
                    TaggedOptionHistoryClassifier S RelS h h') := by
  intro mapH mapH'
  cases mapH with
  | inl absentH =>
      cases mapH' with
      | inl absentH' =>
          exact Or.inl (And.intro absentH.left (And.intro absentH'.left absentH.right))
      | inr presentH' =>
          cases presentH' with
          | intro b dataH' =>
              cases dataH' with
              | intro _sourceB restH' =>
                  cases restH' with
                  | intro _targetB restH' =>
                      cases restH' with
                      | intro _sameH'Present sameKPresentB =>
                          exact False.elim
                            (not_hsame_emp_e1
                              (hsame_trans (hsame_symm absentH.right) sameKPresentB))
  | inr presentH =>
      cases presentH with
      | intro a dataH =>
          cases dataH with
          | intro sourceA restH =>
              cases restH with
              | intro targetA restH =>
                  cases restH with
                  | intro sameHPresent sameKPresentA =>
                      cases mapH' with
                      | inl absentH' =>
                          exact False.elim
                            (not_hsame_e1_empty
                              (hsame_trans (hsame_symm sameKPresentA) absentH'.right))
                      | inr presentH' =>
                          cases presentH' with
                          | intro b dataH' =>
                              cases dataH' with
                              | intro sourceB restH' =>
                                  cases restH' with
                                  | intro targetB restH' =>
                                      cases restH' with
                                      | intro sameH'Present sameKPresentB =>
                                          have sameMapped :
                                              hsame (delta.map a) (delta.map b) :=
                                            hsame_e1_iff.mp
                                              (hsame_trans (hsame_symm sameKPresentA)
                                                sameKPresentB)
                                          have relAB : RelS a b :=
                                            reflects a b sourceA sourceB sameMapped
                                          exact Or.inr
                                            ⟨a, b, sourceA, sourceB, relAB, targetA, targetB,
                                              sameHPresent, sameH'Present, sameKPresentA,
                                              sameKPresentB,
                                              Or.inr
                                                ⟨a, b, sourceA, sourceB, sameHPresent,
                                                  sameH'Present, relAB⟩⟩

end BEDC.Derived.OptionUp
