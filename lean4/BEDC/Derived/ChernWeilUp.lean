import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ChernWeilUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ChernWeilSourceEnvelope
    (curvature derham polynomial connectionLedger characteristic provenance endpoint : BHist) :
    Prop :=
  UnaryHistory curvature ∧ UnaryHistory derham ∧ UnaryHistory polynomial ∧
    UnaryHistory connectionLedger ∧ Cont curvature polynomial characteristic ∧
      Cont characteristic derham provenance ∧ Cont provenance connectionLedger endpoint

theorem ChernWeilSourceEnvelope_carrier_obligation
    {curvature derham polynomial connectionLedger characteristic provenance endpoint : BHist} :
    ChernWeilSourceEnvelope curvature derham polynomial connectionLedger characteristic provenance
      endpoint ->
      UnaryHistory characteristic ∧ UnaryHistory provenance ∧ UnaryHistory endpoint ∧
        hsame characteristic (append curvature polynomial) ∧
          hsame provenance (append characteristic derham) ∧
            hsame endpoint (append provenance connectionLedger) := by
  intro envelope
  have curvatureUnary : UnaryHistory curvature := envelope.left
  have derhamUnary : UnaryHistory derham := envelope.right.left
  have polynomialUnary : UnaryHistory polynomial := envelope.right.right.left
  have connectionLedgerUnary : UnaryHistory connectionLedger := envelope.right.right.right.left
  have characteristicReadback : Cont curvature polynomial characteristic :=
    envelope.right.right.right.right.left
  have provenanceReadback : Cont characteristic derham provenance :=
    envelope.right.right.right.right.right.left
  have endpointReadback : Cont provenance connectionLedger endpoint :=
    envelope.right.right.right.right.right.right
  have characteristicUnary : UnaryHistory characteristic :=
    unary_cont_closed curvatureUnary polynomialUnary characteristicReadback
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed characteristicUnary derhamUnary provenanceReadback
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary connectionLedgerUnary endpointReadback
  exact And.intro characteristicUnary
    (And.intro provenanceUnary
      (And.intro endpointUnary
        (And.intro characteristicReadback
          (And.intro provenanceReadback endpointReadback))))

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

def ChernWeilSourceProjectionEnvelope
    (curvature derham provenance connectionLedger classRow : BHist) : Prop :=
  UnaryHistory curvature ∧
    UnaryHistory derham ∧
      UnaryHistory connectionLedger ∧
        Cont curvature derham provenance ∧ Cont provenance connectionLedger classRow

theorem ChernWeilSourceEnvelope_projection_rows
    {curvature derham provenance connectionLedger classRow : BHist} :
    ChernWeilSourceProjectionEnvelope curvature derham provenance connectionLedger classRow ->
      UnaryHistory curvature ∧
        UnaryHistory derham ∧
          UnaryHistory connectionLedger ∧
            UnaryHistory provenance ∧
              UnaryHistory classRow ∧
                Cont curvature derham provenance ∧
                  Cont provenance connectionLedger classRow ∧
                    hsame classRow (append (append curvature derham) connectionLedger) := by
  intro envelope
  unfold ChernWeilSourceProjectionEnvelope at envelope
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
