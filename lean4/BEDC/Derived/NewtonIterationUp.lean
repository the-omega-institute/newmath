import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Unary

namespace BEDC.Derived.NewtonIterationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def NewtonIterationBHistCarrier
    (derivative banach point derivativeRow inverse next stepLedger provenance endpoint : BHist) :
    Prop :=
  UnaryHistory derivative ∧ UnaryHistory banach ∧ UnaryHistory point ∧
    UnaryHistory derivativeRow ∧ UnaryHistory inverse ∧ UnaryHistory provenance ∧
      Cont point derivativeRow stepLedger ∧ Cont stepLedger inverse next ∧
        Cont provenance next endpoint

theorem NewtonIterationBHistCarrier_banach_derivative_source_scope
    {derivative banach point derivativeRow inverse next stepLedger provenance endpoint : BHist} :
    NewtonIterationBHistCarrier derivative banach point derivativeRow inverse next stepLedger
      provenance endpoint ->
      UnaryHistory derivative ∧ UnaryHistory banach ∧ UnaryHistory point ∧
        UnaryHistory derivativeRow ∧ UnaryHistory inverse ∧ UnaryHistory stepLedger ∧
          UnaryHistory next ∧ UnaryHistory endpoint ∧ Cont point derivativeRow stepLedger ∧
            Cont stepLedger inverse next ∧ Cont provenance next endpoint ∧
              hsame endpoint (append provenance next) := by
  intro carrier
  have derivativeUnary : UnaryHistory derivative := carrier.left
  have banachUnary : UnaryHistory banach := carrier.right.left
  have pointUnary : UnaryHistory point := carrier.right.right.left
  have derivativeRowUnary : UnaryHistory derivativeRow := carrier.right.right.right.left
  have inverseUnary : UnaryHistory inverse := carrier.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := carrier.right.right.right.right.right.left
  have pointDerivative : Cont point derivativeRow stepLedger :=
    carrier.right.right.right.right.right.right.left
  have stepInverse : Cont stepLedger inverse next :=
    carrier.right.right.right.right.right.right.right.left
  have provenanceNext : Cont provenance next endpoint :=
    carrier.right.right.right.right.right.right.right.right
  have stepLedgerUnary : UnaryHistory stepLedger :=
    unary_cont_closed pointUnary derivativeRowUnary pointDerivative
  have nextUnary : UnaryHistory next :=
    unary_cont_closed stepLedgerUnary inverseUnary stepInverse
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary nextUnary provenanceNext
  exact
    ⟨derivativeUnary,
      banachUnary,
      pointUnary,
      derivativeRowUnary,
      inverseUnary,
      stepLedgerUnary,
      nextUnary,
      endpointUnary,
      pointDerivative,
      stepInverse,
      provenanceNext,
      provenanceNext⟩

theorem NewtonIterationStep_stability
    {derivative derivative' banach banach' point point' inverse inverse' next next' step
      step' ledger ledger' : BHist} :
    UnaryHistory derivative -> UnaryHistory banach -> UnaryHistory point ->
      UnaryHistory inverse -> hsame derivative derivative' -> hsame banach banach' ->
        hsame point point' -> hsame inverse inverse' -> Cont derivative point step ->
          Cont derivative' point' step' -> Cont step inverse ledger ->
            Cont step' inverse' ledger' -> Cont ledger banach next ->
              Cont ledger' banach' next' ->
                UnaryHistory step' ∧ UnaryHistory ledger' ∧ UnaryHistory next' ∧
                  hsame step step' ∧ hsame ledger ledger' ∧ hsame next next' := by
  intro derivativeUnary banachUnary pointUnary inverseUnary sameDerivative sameBanach samePoint
    sameInverse stepCont stepCont' ledgerCont ledgerCont' nextCont nextCont'
  have derivativeUnary' : UnaryHistory derivative' :=
    unary_transport derivativeUnary sameDerivative
  have pointUnary' : UnaryHistory point' :=
    unary_transport pointUnary samePoint
  have inverseUnary' : UnaryHistory inverse' :=
    unary_transport inverseUnary sameInverse
  have banachUnary' : UnaryHistory banach' :=
    unary_transport banachUnary sameBanach
  have stepUnary' : UnaryHistory step' :=
    unary_cont_closed derivativeUnary' pointUnary' stepCont'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed stepUnary' inverseUnary' ledgerCont'
  have nextUnary' : UnaryHistory next' :=
    unary_cont_closed ledgerUnary' banachUnary' nextCont'
  have sameStep : hsame step step' :=
    cont_respects_hsame sameDerivative samePoint stepCont stepCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameStep sameInverse ledgerCont ledgerCont'
  have sameNext : hsame next next' :=
    cont_respects_hsame sameLedger sameBanach nextCont nextCont'
  exact And.intro stepUnary'
    (And.intro ledgerUnary'
      (And.intro nextUnary'
        (And.intro sameStep
          (And.intro sameLedger sameNext))))

theorem NewtonIterationBHistCarrier_step_endpoint_transport
    {derivative banach point point' derivativeRow derivativeRow' inverse inverse' next next'
      stepLedger stepLedger' provenance endpoint endpoint' : BHist} :
    NewtonIterationBHistCarrier derivative banach point derivativeRow inverse next stepLedger
        provenance endpoint ->
      hsame point point' ->
        hsame derivativeRow derivativeRow' ->
          hsame inverse inverse' ->
            Cont point' derivativeRow' stepLedger' ->
              Cont stepLedger' inverse' next' ->
                Cont provenance next' endpoint' ->
                  NewtonIterationBHistCarrier derivative banach point' derivativeRow' inverse'
                      next' stepLedger' provenance endpoint' ∧
                    hsame stepLedger stepLedger' ∧ hsame next next' ∧
                      hsame endpoint endpoint' := by
  intro carrier samePoint sameDerivativeRow sameInverse stepLedgerRow' nextRow' endpointRow'
  have sameStepLedger : hsame stepLedger stepLedger' :=
    cont_respects_hsame samePoint sameDerivativeRow
      carrier.right.right.right.right.right.right.left stepLedgerRow'
  have sameNext : hsame next next' :=
    cont_respects_hsame sameStepLedger sameInverse
      carrier.right.right.right.right.right.right.right.left nextRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_refl provenance) sameNext
      carrier.right.right.right.right.right.right.right.right endpointRow'
  have transportedCarrier :
      NewtonIterationBHistCarrier derivative banach point' derivativeRow' inverse' next'
        stepLedger' provenance endpoint' :=
    ⟨carrier.left,
      carrier.right.left,
      unary_transport carrier.right.right.left samePoint,
      unary_transport carrier.right.right.right.left sameDerivativeRow,
      unary_transport carrier.right.right.right.right.left sameInverse,
      carrier.right.right.right.right.right.left,
      stepLedgerRow',
      nextRow',
      endpointRow'⟩
  exact And.intro transportedCarrier
    (And.intro sameStepLedger (And.intro sameNext sameEndpoint))

end BEDC.Derived.NewtonIterationUp
