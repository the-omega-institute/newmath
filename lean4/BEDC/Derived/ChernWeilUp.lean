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

def ChernWeilSourceEnvelope
    (curvature derham provenance connectionLedger classRow : BHist) : Prop :=
  UnaryHistory curvature ∧
    UnaryHistory derham ∧
      UnaryHistory connectionLedger ∧
        Cont curvature derham provenance ∧ Cont provenance connectionLedger classRow

theorem ChernWeilSourceEnvelope_projection_rows
    {curvature derham provenance connectionLedger classRow : BHist} :
    ChernWeilSourceEnvelope curvature derham provenance connectionLedger classRow ->
      UnaryHistory curvature ∧
        UnaryHistory derham ∧
          UnaryHistory connectionLedger ∧
            UnaryHistory provenance ∧
              UnaryHistory classRow ∧
                Cont curvature derham provenance ∧
                  Cont provenance connectionLedger classRow ∧
                    hsame classRow (append (append curvature derham) connectionLedger) := by
  intro envelope
  unfold ChernWeilSourceEnvelope at envelope
  have unaryCurvature : UnaryHistory curvature := envelope.left
  have unaryDerham : UnaryHistory derham := envelope.right.left
  have unaryLedger : UnaryHistory connectionLedger := envelope.right.right.left
  have curvatureDerham : Cont curvature derham provenance := envelope.right.right.right.left
  have ledgerClass : Cont provenance connectionLedger classRow := envelope.right.right.right.right
  have unaryProvenance : UnaryHistory provenance :=
    unary_cont_closed unaryCurvature unaryDerham curvatureDerham
  have unaryClassRow : UnaryHistory classRow :=
    unary_cont_closed unaryProvenance unaryLedger ledgerClass
  have readback : hsame classRow (append (append curvature derham) connectionLedger) :=
    ledgerClass.trans (congrArg (fun row => append row connectionLedger) curvatureDerham)
  exact And.intro unaryCurvature
    (And.intro unaryDerham
      (And.intro unaryLedger
        (And.intro unaryProvenance
          (And.intro unaryClassRow
            (And.intro curvatureDerham (And.intro ledgerClass readback))))))

end BEDC.Derived.ChernWeilUp
