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

end BEDC.Derived.ChernWeilUp
