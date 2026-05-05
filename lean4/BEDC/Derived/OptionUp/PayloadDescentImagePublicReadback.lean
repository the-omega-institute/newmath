import BEDC.Derived.OptionUp.PayloadDescent

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageCarrier_public_readback_single_valued
    {S T : BHist -> Prop} {RelS RelT : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT) {k : BHist} :
    TaggedOptionPayloadDescentImageCarrier S T delta k ->
      TaggedOptionHistoryCarrier T k ∧
        ((hsame k BHist.Empty ∧
            ((exists a : BHist, S a ∧ T (delta.map a) ∧
                hsame k (BHist.e1 (delta.map a))) -> False)) ∨
          (exists a : BHist,
            S a ∧ T (delta.map a) ∧ hsame k (BHist.e1 (delta.map a)) ∧
              (hsame k BHist.Empty -> False) ∧
                (forall b : BHist, S b -> T (delta.map b) ->
                  hsame k (BHist.e1 (delta.map b)) ->
                    hsame (delta.map a) (delta.map b)))) := by
  intro image
  have branch := (TaggedOptionPayloadDescentImageCarrier_branch_exactness delta).mp image
  have targetCarrier : TaggedOptionHistoryCarrier T k := by
    cases branch with
    | inl absent =>
        exact Or.inl absent
    | inr present =>
        cases present with
        | intro a data =>
            exact Or.inr (Exists.intro (delta.map a) (And.intro data.right.left data.right.right))
  refine And.intro targetCarrier ?_
  cases branch with
  | inl absent =>
      exact Or.inl
        (And.intro absent
          (by
            intro present
            cases present with
            | intro a data =>
                exact not_hsame_emp_e1
                  (hsame_trans (hsame_symm absent) data.right.right)))
  | inr present =>
      cases present with
      | intro a data =>
          exact Or.inr
            (Exists.intro a
              (And.intro data.left
                (And.intro data.right.left
                  (And.intro data.right.right
                    (And.intro
                      (by
                        intro absent
                        exact not_hsame_emp_e1
                          (hsame_trans (hsame_symm absent) data.right.right))
                      (by
                        intro b _sourceB _targetB sameKB
                        exact hsame_e1_iff.mp
                          (hsame_trans (hsame_symm data.right.right) sameKB)))))))

end BEDC.Derived.OptionUp
