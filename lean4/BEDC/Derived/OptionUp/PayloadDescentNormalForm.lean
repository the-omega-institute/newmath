import BEDC.Derived.OptionUp.PayloadDescent

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionMapRel_constructor_normal_form {S T : BHist -> Prop}
    {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT) {h k : BHist} :
    TaggedOptionMapRel S T delta h k ->
      (∀ t : BHist, (hsame h (BHist.e0 t) -> False) ∧
        (hsame k (BHist.e0 t) -> False)) ∧
        (hsame h BHist.Empty <-> hsame k BHist.Empty) ∧
          ((∃ a : BHist, S a ∧ hsame h (BHist.e1 a)) <->
            (∃ b : BHist, T b ∧ hsame k (BHist.e1 b))) ∧
            (∀ u v : BHist, S u -> hsame h (BHist.e1 u) -> T v ->
              hsame k (BHist.e1 v) ->
                ∃ a : BHist,
                  S a ∧ T (delta.map a) ∧ hsame u a ∧ hsame v (delta.map a)) := by
  intro mapRel
  have visible := TaggedOptionMapRel_visible_branch_equivalence delta mapRel
  have zero :
      ∀ t : BHist, (hsame h (BHist.e0 t) -> False) ∧
        (hsame k (BHist.e0 t) -> False) := by
    intro t
    constructor
    · intro sameHE0
      cases mapRel with
      | inl absent =>
          exact not_hsame_emp_e0 (hsame_trans (hsame_symm absent.left) sameHE0)
      | inr present =>
          cases present with
          | intro _a data =>
              exact not_hsame_e1_e0 (hsame_trans (hsame_symm data.right.right.left) sameHE0)
    · intro sameKE0
      cases mapRel with
      | inl absent =>
          exact not_hsame_emp_e0 (hsame_trans (hsame_symm absent.right) sameKE0)
      | inr present =>
          cases present with
          | intro _a data =>
              exact not_hsame_e1_e0 (hsame_trans (hsame_symm data.right.right.right) sameKE0)
  have readback :
      ∀ u v : BHist, S u -> hsame h (BHist.e1 u) -> T v ->
        hsame k (BHist.e1 v) ->
          ∃ a : BHist,
            S a ∧ T (delta.map a) ∧ hsame u a ∧ hsame v (delta.map a) := by
    intro u v _sourceU sameHU _targetV sameKV
    cases mapRel with
    | inl absent =>
        exact False.elim
          (not_hsame_emp_e1 (hsame_trans (hsame_symm absent.left) sameHU))
    | inr present =>
        cases present with
        | intro a data =>
            have sameUA : hsame u a :=
              hsame_e1_iff.mp (hsame_trans (hsame_symm sameHU) data.right.right.left)
            have sameVMap : hsame v (delta.map a) :=
              hsame_e1_iff.mp (hsame_trans (hsame_symm sameKV) data.right.right.right)
            exact Exists.intro a
              (And.intro data.left
                (And.intro data.right.left (And.intro sameUA sameVMap)))
  exact And.intro zero (And.intro visible.left (And.intro visible.right readback))

end BEDC.Derived.OptionUp
