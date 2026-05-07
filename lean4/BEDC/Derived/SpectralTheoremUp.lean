import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.SpectralTheoremUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SpectralTheoremCarrier
    (endpoint operator spectrum projection calculus provenance : BHist) : Prop :=
  UnaryHistory operator ∧ UnaryHistory spectrum ∧ UnaryHistory calculus ∧
    Cont operator spectrum projection ∧ Cont projection calculus endpoint ∧
      hsame provenance endpoint

theorem SpectralTheoremCarrier_classifier_transport
    {endpoint endpoint' operator spectrum projection calculus provenance : BHist} :
    SpectralTheoremCarrier endpoint operator spectrum projection calculus provenance ->
      hsame endpoint endpoint' ->
        SpectralTheoremCarrier endpoint' operator spectrum projection calculus endpoint' ∧
          Cont projection calculus endpoint' ∧ UnaryHistory endpoint' ∧
            hsame provenance endpoint' := by
  intro carrier sameEndpoint
  have transportedEndpoint : Cont projection calculus endpoint' :=
    cont_result_hsame_transport carrier.right.right.right.right.left sameEndpoint
  have projectionUnary : UnaryHistory projection :=
    unary_cont_closed carrier.left carrier.right.left carrier.right.right.right.left
  have endpointUnary : UnaryHistory endpoint' :=
    unary_transport
      (unary_cont_closed projectionUnary carrier.right.right.left
        carrier.right.right.right.right.left)
      sameEndpoint
  have provenanceSame : hsame provenance endpoint' :=
    hsame_trans carrier.right.right.right.right.right sameEndpoint
  exact And.intro
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro carrier.right.right.right.left
            (And.intro transportedEndpoint (hsame_refl endpoint'))))))
    (And.intro transportedEndpoint (And.intro endpointUnary provenanceSame))

end BEDC.Derived.SpectralTheoremUp
