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

theorem TaggedOptionMapRel_common_source_visible_target_completion {S T : BHist -> Prop}
    {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (certT : NameCert T RelT)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    (target_hsame : TaggedOptionSourceHsameCompatible T RelT) {h k k' : BHist} :
    TaggedOptionMapRel S T delta h k ->
      TaggedOptionMapRel S T delta h k' ->
        (forall {x : BHist}, T x -> hsame k (BHist.e1 x) ->
          exists y : BHist, T y ∧ hsame k' (BHist.e1 y) ∧ RelT x y) ∧
        (forall {y : BHist}, T y -> hsame k' (BHist.e1 y) ->
          exists x : BHist, T x ∧ hsame k (BHist.e1 x) ∧ RelT x y) := by
  intro mapK mapK'
  have targetClass : TaggedOptionHistoryClassifier T RelT k k' :=
    TaggedOptionMapRel_common_source_target_classification delta source_hsame mapK mapK'
  constructor
  · intro x targetX sameKX
    cases targetClass with
    | inl absent =>
        exact False.elim (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameKX))
    | inr present =>
        cases present with
        | intro a present =>
            cases present with
            | intro b data =>
                have sameXA : hsame x a :=
                  hsame_e1_iff.mp
                    (hsame_trans (hsame_symm sameKX) data.right.right.left)
                have relXA : RelT x a :=
                  target_hsame targetX data.left sameXA
                have relXB : RelT x b :=
                  NameCert.equiv_trans certT relXA data.right.right.right.right
                exact Exists.intro b
                  (And.intro data.right.left
                    (And.intro data.right.right.right.left relXB))
  · intro y targetY sameK'Y
    cases targetClass with
    | inl absent =>
        exact False.elim (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.right) sameK'Y))
    | inr present =>
        cases present with
        | intro a present =>
            cases present with
            | intro b data =>
                have sameBY : hsame b y :=
                  hsame_e1_iff.mp
                    (hsame_trans (hsame_symm data.right.right.right.left) sameK'Y)
                have relBY : RelT b y :=
                  target_hsame data.right.left targetY sameBY
                have relAY : RelT a y :=
                  NameCert.equiv_trans certT data.right.right.right.right relBY
                exact Exists.intro a
                  (And.intro data.left (And.intro data.right.right.left relAY))

end BEDC.Derived.OptionUp
