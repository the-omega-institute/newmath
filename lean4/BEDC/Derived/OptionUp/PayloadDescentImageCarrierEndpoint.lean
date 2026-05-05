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

end BEDC.Derived.OptionUp
