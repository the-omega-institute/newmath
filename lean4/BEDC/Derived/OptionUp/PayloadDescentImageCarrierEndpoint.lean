import BEDC.Derived.OptionUp.PayloadDescentImageClassifier

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageCarrier_composite_zero_endpoint_exclusion
    {S U : BHist -> Prop} {RelS RelT RelU : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU) {m t : BHist} :
    TaggedOptionPayloadDescentImageCarrier S U (TaggedOptionDescentComp delta epsilon) m ->
      hsame m (BHist.e0 t) ->
        False := by
  intro image sameZeroEndpoint
  have branch :=
    (TaggedOptionPayloadDescentImageCarrier_branch_exactness
      (TaggedOptionDescentComp delta epsilon)).mp image
  cases branch with
  | inl absent =>
      exact not_hsame_emp_e0 (hsame_trans (hsame_symm absent) sameZeroEndpoint)
  | inr present =>
      cases present with
      | intro a data =>
            exact not_hsame_e1_e0
              (hsame_trans (hsame_symm data.right.right) sameZeroEndpoint)

theorem TaggedOptionPayloadDescentImageClassifier_composite_zero_endpoint_exclusion
    {S U : BHist -> Prop} {RelS RelT RelU : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU) {m m' t : BHist} :
    TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) m
        m' ->
      (hsame m (BHist.e0 t) -> False) ∧ (hsame m' (BHist.e0 t) -> False) := by
  intro image
  cases image with
  | intro h imageRest =>
      cases imageRest with
      | intro h' imageData =>
          cases imageData with
          | intro sourceClassifier maps =>
              cases maps with
              | intro mapLeft mapRight =>
                  constructor
                  · intro sameZeroEndpoint
                    cases sourceClassifier with
                    | inl sourceAbsent =>
                        cases mapLeft with
                        | inl mapAbsent =>
                            exact not_hsame_emp_e0
                              (hsame_trans (hsame_symm mapAbsent.right) sameZeroEndpoint)
                        | inr mapPresent =>
                            cases mapPresent with
                            | intro _a data =>
                                exact not_hsame_e1_e0
                                  (hsame_trans (hsame_symm data.right.right.right)
                                    sameZeroEndpoint)
                    | inr sourcePresent =>
                        cases sourcePresent with
                        | intro _a sourceRest =>
                            cases sourceRest with
                            | intro _b _sourceData =>
                                cases mapLeft with
                                | inl mapAbsent =>
                                    exact not_hsame_emp_e0
                                      (hsame_trans (hsame_symm mapAbsent.right)
                                        sameZeroEndpoint)
                                | inr mapPresent =>
                                    cases mapPresent with
                                    | intro _a0 data =>
                                        exact not_hsame_e1_e0
                                          (hsame_trans (hsame_symm data.right.right.right)
                                            sameZeroEndpoint)
                  · intro sameZeroEndpoint
                    cases sourceClassifier with
                    | inl sourceAbsent =>
                        cases mapRight with
                        | inl mapAbsent =>
                            exact not_hsame_emp_e0
                              (hsame_trans (hsame_symm mapAbsent.right) sameZeroEndpoint)
                        | inr mapPresent =>
                            cases mapPresent with
                            | intro _b data =>
                                exact not_hsame_e1_e0
                                  (hsame_trans (hsame_symm data.right.right.right)
                                    sameZeroEndpoint)
                    | inr sourcePresent =>
                        cases sourcePresent with
                        | intro _a sourceRest =>
                            cases sourceRest with
                            | intro _b _sourceData =>
                                cases mapRight with
                                | inl mapAbsent =>
                                    exact not_hsame_emp_e0
                                      (hsame_trans (hsame_symm mapAbsent.right)
                                        sameZeroEndpoint)
                                | inr mapPresent =>
                                    cases mapPresent with
                                    | intro _b0 data =>
                                        exact not_hsame_e1_e0
                                          (hsame_trans (hsame_symm data.right.right.right)
                                            sameZeroEndpoint)

end BEDC.Derived.OptionUp
