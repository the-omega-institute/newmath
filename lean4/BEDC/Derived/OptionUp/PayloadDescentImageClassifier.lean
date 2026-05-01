import BEDC.Derived.OptionUp.PayloadDescent

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def TaggedOptionPayloadDescentImageClassifier (S T : BHist → Prop)
    {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT) (k k' : BHist) : Prop :=
  ∃ h h' : BHist,
    TaggedOptionHistoryClassifier S RelS h h' ∧ TaggedOptionMapRel S T delta h k ∧
      TaggedOptionMapRel S T delta h' k'

theorem TaggedOptionPayloadDescentImageClassifier_branch_exactness {S T : BHist → Prop}
    {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {k k' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k k' ↔
      (hsame k BHist.Empty ∧ hsame k' BHist.Empty) ∨
        ∃ a b : BHist,
          S a ∧ S b ∧ RelS a b ∧ T (delta.map a) ∧ T (delta.map b) ∧
            hsame k (BHist.e1 (delta.map a)) ∧ hsame k' (BHist.e1 (delta.map b)) := by
  constructor
  · intro image
    cases image with
    | intro h image =>
        cases image with
        | intro h' image =>
            cases image with
            | intro sourceClass maps =>
                cases maps with
                | intro mapH mapH' =>
                    cases sourceClass with
                    | inl absent =>
                        cases mapH with
                        | inl mapAbsent =>
                            cases mapH' with
                            | inl mapAbsent' =>
                                exact Or.inl (And.intro mapAbsent.right mapAbsent'.right)
                            | inr mapPresent' =>
                                cases mapPresent' with
                                | intro _a data =>
                                    exact False.elim
                                      (not_hsame_emp_e1
                                        (hsame_trans (hsame_symm absent.right)
                                          data.right.right.left))
                        | inr mapPresent =>
                            cases mapPresent with
                            | intro _a data =>
                                exact False.elim
                                  (not_hsame_emp_e1
                                    (hsame_trans (hsame_symm absent.left)
                                      data.right.right.left))
                    | inr present =>
                        cases present with
                        | intro a present =>
                            cases present with
                            | intro b data =>
                                cases mapH with
                                | inl mapAbsent =>
                                    exact False.elim
                                      (not_hsame_emp_e1
                                        (hsame_trans (hsame_symm mapAbsent.left)
                                          data.right.right.left))
                                | inr mapPresent =>
                                    cases mapPresent with
                                    | intro a0 dataA0 =>
                                        cases mapH' with
                                        | inl mapAbsent' =>
                                            exact False.elim
                                              (not_hsame_emp_e1
                                                (hsame_trans (hsame_symm mapAbsent'.left)
                                                  data.right.right.right.left))
                                        | inr mapPresent' =>
                                            cases mapPresent' with
                                            | intro b0 dataB0 =>
                                                have sameA0A : hsame a0 a :=
                                                  hsame_e1_iff.mp
                                                    (hsame_trans
                                                      (hsame_symm dataA0.right.right.left)
                                                      data.right.right.left)
                                                have sameBB0 : hsame b b0 :=
                                                  hsame_e1_iff.mp
                                                    (hsame_trans
                                                      (hsame_symm data.right.right.right.left)
                                                      dataB0.right.right.left)
                                                have relA0A : RelS a0 a :=
                                                  source_hsame dataA0.left data.left sameA0A
                                                have relBB0 : RelS b b0 :=
                                                  source_hsame data.right.left dataB0.left sameBB0
                                                have relA0B : RelS a0 b :=
                                                  NameCert.equiv_trans cert relA0A
                                                    data.right.right.right.right
                                                have relA0B0 : RelS a0 b0 :=
                                                  NameCert.equiv_trans cert relA0B relBB0
                                                exact Or.inr
                                                  (Exists.intro a0
                                                    (Exists.intro b0
                                                      (And.intro dataA0.left
                                                        (And.intro dataB0.left
                                                          (And.intro relA0B0
                                                            (And.intro dataA0.right.left
                                                              (And.intro dataB0.right.left
                                                                (And.intro
                                                                  dataA0.right.right.right
                                                                  dataB0.right.right.right))))))))
  · intro branch
    cases branch with
    | inl absent =>
        exact ⟨BHist.Empty, BHist.Empty,
          Or.inl (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)),
          Or.inl (And.intro (hsame_refl BHist.Empty) absent.left),
          Or.inl (And.intro (hsame_refl BHist.Empty) absent.right)⟩
    | inr present =>
        cases present with
        | intro a present =>
            cases present with
            | intro b data =>
                exact ⟨BHist.e1 a, BHist.e1 b,
                  Or.inr
                    ⟨a, b, data.left, data.right.left, hsame_refl (BHist.e1 a),
                      hsame_refl (BHist.e1 b), data.right.right.left⟩,
                  Or.inr
                    ⟨a, data.left, data.right.right.right.left,
                      hsame_refl (BHist.e1 a), data.right.right.right.right.right.left⟩,
                  Or.inr
                    ⟨b, data.right.left, data.right.right.right.right.left,
                      hsame_refl (BHist.e1 b), data.right.right.right.right.right.right⟩⟩

def TaggedOptionPayloadDescentReflectsSource (S : BHist → Prop)
    {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT) : Prop :=
  ∀ a b : BHist, S a → S b → hsame (delta.map a) (delta.map b) → RelS a b

theorem TaggedOptionPayloadDescentImageClassifier_reflective_transitivity
    {S T : BHist → Prop} {RelS RelT : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (cert : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (reflects : TaggedOptionPayloadDescentReflectsSource S delta) {k l m : BHist} :
    TaggedOptionPayloadDescentImageClassifier S T delta k l →
      TaggedOptionPayloadDescentImageClassifier S T delta l m →
        TaggedOptionPayloadDescentImageClassifier S T delta k m := by
  intro left right
  have exactLeft :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp left
  have exactRight :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mp right
  apply
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness delta cert source_hsame).mpr
  cases exactLeft with
  | inl absentLeft =>
      cases exactRight with
      | inl absentRight =>
          exact Or.inl (And.intro absentLeft.left absentRight.right)
      | inr presentRight =>
          cases presentRight with
          | intro _c presentRight =>
              cases presentRight with
              | intro _d dataRight =>
                  exact False.elim
                    (not_hsame_emp_e1
                      (hsame_trans (hsame_symm absentLeft.right)
                        dataRight.right.right.right.right.right.left))
  | inr presentLeft =>
      cases presentLeft with
      | intro a presentLeft =>
          cases presentLeft with
          | intro b dataLeft =>
              cases exactRight with
              | inl absentRight =>
                  exact False.elim
                    (not_hsame_e1_empty
                      (hsame_trans
                        (hsame_symm dataLeft.right.right.right.right.right.right)
                        absentRight.left))
              | inr presentRight =>
                  cases presentRight with
                  | intro c presentRight =>
                      cases presentRight with
                      | intro d dataRight =>
                          have sameBC : hsame (delta.map b) (delta.map c) :=
                            hsame_e1_iff.mp
                              (hsame_trans
                                (hsame_symm dataLeft.right.right.right.right.right.right)
                                dataRight.right.right.right.right.right.left)
                          have relBC : RelS b c :=
                            reflects b c dataLeft.right.left dataRight.left sameBC
                          have relAC : RelS a c :=
                            NameCert.equiv_trans cert dataLeft.right.right.left relBC
                          have relAD : RelS a d :=
                            NameCert.equiv_trans cert relAC dataRight.right.right.left
                          exact Or.inr
                            (Exists.intro a
                              (Exists.intro d
                                (And.intro dataLeft.left
                                  (And.intro dataRight.right.left
                                    (And.intro relAD
                                      (And.intro dataLeft.right.right.right.left
                                        (And.intro dataRight.right.right.right.right.left
                                          (And.intro dataLeft.right.right.right.right.right.left
                                            dataRight.right.right.right.right.right.right))))))))

end BEDC.Derived.OptionUp
