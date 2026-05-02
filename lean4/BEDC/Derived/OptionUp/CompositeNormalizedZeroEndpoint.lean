import BEDC.Derived.OptionUp.PayloadDescentImageClassifierReadback

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageClassifier_composite_normalized_zero_endpoint_exclusion
    {S U : BHist → Prop} {RelS RelT RelU : BHist → BHist → Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (certS : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS)
    {m m' u u' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) m m' →
      hsame m u →
        hsame m' u' →
          ∀ t : BHist, (hsame u (BHist.e0 t) → False) ∧
            (hsame u' (BHist.e0 t) → False) := by
  intro image sameMU sameM'U' t
  have transported :
      TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) u u' :=
    TaggedOptionPayloadDescentImageClassifier_hsame_transport
      (TaggedOptionDescentComp delta epsilon) certS source_hsame image sameMU sameM'U'
  have branch :=
    (TaggedOptionPayloadDescentImageClassifier_branch_exactness
      (TaggedOptionDescentComp delta epsilon) certS source_hsame).mp transported
  constructor
  · intro sameUE0
    cases branch with
    | inl absent =>
        exact not_hsame_emp_e0 (hsame_trans (hsame_symm absent.left) sameUE0)
    | inr present =>
        cases present with
        | intro _a present =>
            cases present with
            | intro _b data =>
                exact not_hsame_e1_e0
                  (hsame_trans (hsame_symm data.right.right.right.right.right.left) sameUE0)
  · intro sameU'E0
    cases branch with
    | inl absent =>
        exact not_hsame_emp_e0 (hsame_trans (hsame_symm absent.right) sameU'E0)
    | inr present =>
        cases present with
        | intro _a present =>
            cases present with
            | intro _b data =>
                exact not_hsame_e1_e0
                  (hsame_trans (hsame_symm data.right.right.right.right.right.right) sameU'E0)

end BEDC.Derived.OptionUp
