import BEDC.Derived.TreeUp

namespace BEDC.Derived.TreeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem TreeBHistCarrier_classifier_obligation
    {graph edge connected acyclic root endpoint : BHist} :
    TreeBHistCarrier graph edge connected acyclic root endpoint ->
      hsame endpoint endpoint ∧
        (∀ endpoint' : BHist, hsame endpoint endpoint' ->
          TreeBHistCarrier graph edge connected acyclic root endpoint' ∧
            TreeRootBranch endpoint' root connected ∧ UnaryHistory root ∧
              Cont endpoint' root connected) ∧
          (∀ endpoint' endpoint'' : BHist, hsame endpoint endpoint' ->
            hsame endpoint' endpoint'' -> hsame endpoint endpoint'') := by
  intro carrier
  constructor
  · exact hsame_refl endpoint
  constructor
  · intro endpoint' sameEndpoint
    have transportedCarrier :
        TreeBHistCarrier graph edge connected acyclic root endpoint' :=
      (TreeBHistCarrier_classifier_transport carrier (hsame_refl graph)
        (hsame_refl edge) (hsame_refl connected) (hsame_refl acyclic)
        (hsame_refl root) sameEndpoint).left
    have branch :
        TreeRootBranch endpoint' root connected ∧ UnaryHistory root ∧
          Cont endpoint' root connected :=
      TreeBHistCarrier_root_branch_transport carrier sameEndpoint (hsame_refl root)
        (hsame_refl connected)
    exact And.intro transportedCarrier branch
  · intro endpoint' endpoint'' sameEndpoint sameEndpoint'
    exact hsame_trans sameEndpoint sameEndpoint'

end BEDC.Derived.TreeUp
