import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ChernWeilUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ChernWeilSourceEnvelope_public_rows
    {curvature derham polynomial endpoint representative classRow provenance ledger : BHist} :
    UnaryHistory curvature ->
      UnaryHistory derham ->
        UnaryHistory polynomial ->
          UnaryHistory provenance ->
            Cont curvature polynomial endpoint ->
              Cont endpoint derham representative ->
                Cont representative provenance ledger ->
                  hsame classRow ledger ->
                    UnaryHistory endpoint ∧ UnaryHistory representative ∧ UnaryHistory ledger ∧
                      hsame endpoint (append curvature polynomial) ∧
                        hsame representative (append (append curvature polynomial) derham) ∧
                          hsame ledger
                            (append (append (append curvature polynomial) derham) provenance) ∧
                            hsame classRow ledger := by
  intro curvatureUnary derhamUnary polynomialUnary provenanceUnary endpointCont representativeCont
    ledgerCont sameClassLedger
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed curvatureUnary polynomialUnary endpointCont
  have representativeUnary : UnaryHistory representative :=
    unary_cont_closed endpointUnary derhamUnary representativeCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed representativeUnary provenanceUnary ledgerCont
  have representativeReadback : hsame representative (append (append curvature polynomial) derham) :=
    hsame_trans representativeCont
      (congrArg (fun h : BHist => append h derham) endpointCont)
  have ledgerReadback :
      hsame ledger (append (append (append curvature polynomial) derham) provenance) :=
    hsame_trans ledgerCont
      (congrArg (fun h : BHist => append h provenance) representativeReadback)
  exact And.intro endpointUnary
    (And.intro representativeUnary
      (And.intro ledgerUnary
        (And.intro endpointCont
          (And.intro representativeReadback
            (And.intro ledgerReadback sameClassLedger)))))

def ChernWeilSourceEnvelope
    (curvature derham provenance connectionFace characteristic : BHist) : Prop :=
  UnaryHistory curvature ∧ UnaryHistory derham ∧ UnaryHistory provenance ∧
    Cont curvature derham provenance ∧ Cont provenance connectionFace characteristic ∧
      hsame characteristic (append provenance connectionFace)

theorem ChernWeilSourceEnvelope_rows
    {curvature derham provenance connectionFace characteristic : BHist} :
    ChernWeilSourceEnvelope curvature derham provenance connectionFace characteristic ->
      UnaryHistory curvature ∧ UnaryHistory derham ∧ Cont curvature derham provenance ∧
        Cont provenance connectionFace characteristic ∧
          hsame characteristic (append provenance connectionFace) := by
  intro envelope
  exact
    And.intro envelope.left
      (And.intro envelope.right.left
        (And.intro envelope.right.right.right.left
          (And.intro envelope.right.right.right.right.left
            envelope.right.right.right.right.right)))

def ChernWeilCarrierEnvelope
    (curvature derham polynomial connectionLedger characteristic provenance endpoint : BHist) :
    Prop :=
  UnaryHistory curvature ∧ UnaryHistory derham ∧ UnaryHistory polynomial ∧
    UnaryHistory connectionLedger ∧ Cont curvature polynomial characteristic ∧
      Cont characteristic derham provenance ∧ Cont provenance connectionLedger endpoint

theorem ChernWeilSourceEnvelope_carrier_obligation
    {curvature derham polynomial connectionLedger characteristic provenance endpoint : BHist} :
    ChernWeilCarrierEnvelope curvature derham polynomial connectionLedger characteristic provenance
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
  have classRowReadback : hsame classRow (append provenance connectionLedger') :=
    ledgerClass'
  have envelope' :
      ChernWeilSourceEnvelope curvature' derham provenance connectionLedger' classRow :=
    And.intro curvatureUnary'
      (And.intro envelope.right.left
        (And.intro provenanceUnary
          (And.intro curvatureDerham'
            (And.intro ledgerClass' classRowReadback))))
  exact And.intro envelope' (And.intro classRowUnary classRowReadback)

theorem ChernWeilCarrierEnvelope_characteristic_ledger_exactness
    {curvature derham polynomial connectionLedger characteristic provenance endpoint connectionLedger'
      endpoint' : BHist} :
    ChernWeilCarrierEnvelope curvature derham polynomial connectionLedger characteristic provenance
        endpoint ->
      hsame connectionLedger connectionLedger' ->
        Cont provenance connectionLedger' endpoint' ->
          ChernWeilCarrierEnvelope curvature derham polynomial connectionLedger' characteristic
              provenance endpoint' ∧
            hsame endpoint endpoint' ∧ UnaryHistory endpoint' := by
  intro envelope sameConnectionLedger endpointCont'
  have obligation :=
    ChernWeilSourceEnvelope_carrier_obligation envelope
  have connectionLedgerUnary' : UnaryHistory connectionLedger' :=
    unary_transport envelope.right.right.right.left sameConnectionLedger
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed obligation.right.left connectionLedgerUnary' endpointCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) sameConnectionLedger
      envelope.right.right.right.right.right.right endpointCont'
  have envelope' :
      ChernWeilCarrierEnvelope curvature derham polynomial connectionLedger' characteristic
        provenance endpoint' :=
    And.intro envelope.left
      (And.intro envelope.right.left
        (And.intro envelope.right.right.left
          (And.intro connectionLedgerUnary'
            (And.intro envelope.right.right.right.right.left
              (And.intro envelope.right.right.right.right.right.left endpointCont')))))
  exact And.intro envelope' (And.intro sameEndpoint endpointUnary')

end BEDC.Derived.ChernWeilUp
