import BEDC.FKernel.Unary

namespace BEDC.Derived.ChernWeilUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

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

theorem ChernWeilSourceEnvelope_connection_choice_stability
    {curvature curvature' derham provenance connectionLedger connectionLedger' classRow : BHist} :
    ChernWeilSourceEnvelope curvature derham provenance connectionLedger classRow ->
      hsame curvature curvature' ->
        UnaryHistory connectionLedger' ->
          Cont curvature' derham provenance ->
            Cont provenance connectionLedger' classRow ->
              ChernWeilSourceEnvelope curvature' derham provenance connectionLedger' classRow ∧
                UnaryHistory classRow ∧ hsame classRow (append provenance connectionLedger') := by
  intro envelope sameCurvature connectionLedgerUnary' curvatureDerham' ledgerClass'
  unfold ChernWeilSourceEnvelope at envelope
  have curvatureUnary' : UnaryHistory curvature' :=
    unary_transport envelope.left sameCurvature
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed curvatureUnary' envelope.right.left curvatureDerham'
  have classRowUnary : UnaryHistory classRow :=
    unary_cont_closed provenanceUnary connectionLedgerUnary' ledgerClass'
  have envelope' :
      ChernWeilSourceEnvelope curvature' derham provenance connectionLedger' classRow :=
    And.intro curvatureUnary'
      (And.intro envelope.right.left
        (And.intro connectionLedgerUnary'
          (And.intro curvatureDerham' ledgerClass')))
  exact And.intro envelope' (And.intro classRowUnary ledgerClass')

end BEDC.Derived.ChernWeilUp
