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

theorem NewtonIterationBHistCarrier_finite_step_concatenation_closure
    {derivative banach x0 derivativeRow1 inverse1 x1 ledger1 provenance1 endpoint1
      y1 derivativeRow2 inverse2 x2 ledger2 provenance2 endpoint2 spliceLedger
      combinedEndpoint : BHist} :
    NewtonIterationBHistCarrier derivative banach x0 derivativeRow1 inverse1 x1 ledger1
        provenance1 endpoint1 ->
      NewtonIterationBHistCarrier derivative banach y1 derivativeRow2 inverse2 x2 ledger2
          provenance2 endpoint2 ->
        hsame x1 y1 ->
          Cont endpoint1 endpoint2 spliceLedger ->
            Cont provenance1 spliceLedger combinedEndpoint ->
              UnaryHistory spliceLedger ∧ UnaryHistory combinedEndpoint ∧
                hsame combinedEndpoint (append provenance1 spliceLedger) := by
  intro first second sameSplice endpointSplice combinedRow
  have firstScope :=
    NewtonIterationBHistCarrier_banach_derivative_source_scope first
  have x1Unary : UnaryHistory x1 :=
    firstScope.right.right.right.right.right.right.left
  have y1Unary : UnaryHistory y1 :=
    unary_transport x1Unary sameSplice
  have endpoint1Unary : UnaryHistory endpoint1 :=
    firstScope.right.right.right.right.right.right.right.left
  have derivativeRow2Unary : UnaryHistory derivativeRow2 :=
    second.right.right.right.left
  have inverse2Unary : UnaryHistory inverse2 :=
    second.right.right.right.right.left
  have provenance2Unary : UnaryHistory provenance2 :=
    second.right.right.right.right.right.left
  have ledger2Row : Cont y1 derivativeRow2 ledger2 :=
    second.right.right.right.right.right.right.left
  have x2Row : Cont ledger2 inverse2 x2 :=
    second.right.right.right.right.right.right.right.left
  have endpoint2Row : Cont provenance2 x2 endpoint2 :=
    second.right.right.right.right.right.right.right.right
  have ledger2Unary : UnaryHistory ledger2 :=
    unary_cont_closed y1Unary derivativeRow2Unary ledger2Row
  have x2Unary : UnaryHistory x2 :=
    unary_cont_closed ledger2Unary inverse2Unary x2Row
  have endpoint2Unary : UnaryHistory endpoint2 :=
    unary_cont_closed provenance2Unary x2Unary endpoint2Row
  have provenance1Unary : UnaryHistory provenance1 :=
    first.right.right.right.right.right.left
  have spliceUnary : UnaryHistory spliceLedger :=
    unary_cont_closed endpoint1Unary endpoint2Unary endpointSplice
  have combinedUnary : UnaryHistory combinedEndpoint :=
    unary_cont_closed provenance1Unary spliceUnary combinedRow
  exact ⟨spliceUnary, combinedUnary, combinedRow⟩

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

end BEDC.Derived.NewtonIterationUp
