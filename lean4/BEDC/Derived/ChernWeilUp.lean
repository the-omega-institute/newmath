import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ChernWeilUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ChernWeilCarrierPacket_curvature_polynomial_stability_obligation
    {curvature curvature' polynomial endpoint endpoint' : BHist} :
    UnaryHistory curvature -> UnaryHistory polynomial -> hsame curvature curvature' ->
      Cont curvature polynomial endpoint -> Cont curvature' polynomial endpoint' ->
        UnaryHistory endpoint ∧ UnaryHistory endpoint' ∧ hsame endpoint endpoint' ∧
          Cont curvature polynomial endpoint ∧ Cont curvature' polynomial endpoint' := by
  intro curvatureUnary polynomialUnary sameCurvature endpointCont endpointCont'
  have curvatureUnary' : UnaryHistory curvature' :=
    unary_transport curvatureUnary sameCurvature
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed curvatureUnary polynomialUnary endpointCont
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed curvatureUnary' polynomialUnary endpointCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameCurvature (hsame_refl polynomial) endpointCont endpointCont'
  exact And.intro endpointUnary
    (And.intro endpointUnary'
      (And.intro sameEndpoint
        (And.intro endpointCont endpointCont')))

end BEDC.Derived.ChernWeilUp
