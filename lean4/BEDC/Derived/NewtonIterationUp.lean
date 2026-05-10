import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NewtonIterationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def NewtonIterationCarrier
    (derivativeSource banachSource point derivative inverseRow nextStep derivativeLedger
      banachLedger stepLedger : BHist) : Prop :=
  Cont derivativeSource banachSource derivativeLedger ∧
    UnaryHistory point ∧
      UnaryHistory derivative ∧
        UnaryHistory inverseRow ∧
          UnaryHistory nextStep ∧
            Cont derivativeLedger point derivative ∧
              Cont derivative inverseRow stepLedger ∧
                Cont point stepLedger nextStep ∧ Cont derivativeLedger stepLedger banachLedger

theorem NewtonIterationCarrier_source_scope
    {derivativeSource banachSource point derivative inverseRow nextStep derivativeLedger
      banachLedger stepLedger : BHist} :
    NewtonIterationCarrier derivativeSource banachSource point derivative inverseRow nextStep
        derivativeLedger banachLedger stepLedger ->
      Cont derivativeSource banachSource derivativeLedger ∧
        UnaryHistory point ∧
          UnaryHistory derivative ∧
            UnaryHistory inverseRow ∧
              UnaryHistory nextStep ∧ Cont point stepLedger nextStep := by
  intro carrier
  exact
    And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
            (And.intro carrier.right.right.right.left
              (And.intro carrier.right.right.right.right.left
              carrier.right.right.right.right.right.right.right.left))))

def NewtonIterationStepCarrier
    (derivative banach point deriv inverse next sourceLedger stepLedger : BHist) : Prop :=
  UnaryHistory derivative ∧ UnaryHistory banach ∧ UnaryHistory point ∧ UnaryHistory deriv ∧
    UnaryHistory inverse ∧ Cont derivative point sourceLedger ∧ Cont deriv inverse next ∧
      Cont banach next stepLedger

theorem NewtonIterationStepCarrier_step_stability
    {derivative banach point deriv inverse next sourceLedger stepLedger derivative' banach'
      point' deriv' inverse' next' sourceLedger' stepLedger' : BHist} :
    NewtonIterationStepCarrier derivative banach point deriv inverse next sourceLedger
        stepLedger ->
      hsame derivative derivative' ->
        hsame banach banach' ->
          hsame point point' ->
            hsame deriv deriv' ->
              hsame inverse inverse' ->
                Cont derivative' point' sourceLedger' ->
                  Cont deriv' inverse' next' ->
                    Cont banach' next' stepLedger' ->
                      NewtonIterationStepCarrier derivative' banach' point' deriv' inverse' next'
                          sourceLedger' stepLedger' ∧
                        hsame sourceLedger sourceLedger' ∧ hsame next next' ∧
                          hsame stepLedger stepLedger' := by
  intro carrier sameDerivative sameBanach samePoint sameDeriv sameInverse sourceRow nextRow
    stepRow
  have derivativeUnary : UnaryHistory derivative' :=
    unary_transport carrier.left sameDerivative
  have banachUnary : UnaryHistory banach' :=
    unary_transport carrier.right.left sameBanach
  have pointUnary : UnaryHistory point' :=
    unary_transport carrier.right.right.left samePoint
  have derivUnary : UnaryHistory deriv' :=
    unary_transport carrier.right.right.right.left sameDeriv
  have inverseUnary : UnaryHistory inverse' :=
    unary_transport carrier.right.right.right.right.left sameInverse
  have nextUnary : UnaryHistory next' :=
    unary_cont_closed derivUnary inverseUnary nextRow
  have sameSourceLedger : hsame sourceLedger sourceLedger' :=
    cont_respects_hsame sameDerivative samePoint carrier.right.right.right.right.right.left
      sourceRow
  have sameNext : hsame next next' :=
    cont_respects_hsame sameDeriv sameInverse carrier.right.right.right.right.right.right.left
      nextRow
  have sameStepLedger : hsame stepLedger stepLedger' :=
    cont_respects_hsame sameBanach sameNext carrier.right.right.right.right.right.right.right
      stepRow
  exact And.intro
    (And.intro derivativeUnary
      (And.intro banachUnary
        (And.intro pointUnary
          (And.intro derivUnary
            (And.intro inverseUnary
              (And.intro sourceRow (And.intro nextRow stepRow)))))))
    (And.intro sameSourceLedger (And.intro sameNext sameStepLedger))

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

theorem NewtonIterationCarrier_obligation_package
    {derivativeSource banachSource point derivative inverseRow nextStep derivativeLedger
      banachLedger stepLedger derivativeSourceNext banachSourceNext pointNext derivativeNext
      inverseRowNext nextStepNext derivativeLedgerNext banachLedgerNext stepLedgerNext :
        BHist} :
    NewtonIterationCarrier derivativeSource banachSource point derivative inverseRow nextStep
        derivativeLedger banachLedger stepLedger ->
      hsame derivativeSource derivativeSourceNext ->
        hsame banachSource banachSourceNext ->
          hsame point pointNext ->
            hsame derivative derivativeNext ->
              hsame inverseRow inverseRowNext ->
                Cont derivativeSourceNext banachSourceNext derivativeLedgerNext ->
                  Cont derivativeLedgerNext pointNext derivativeNext ->
                    Cont derivativeNext inverseRowNext stepLedgerNext ->
                      Cont pointNext stepLedgerNext nextStepNext ->
                        Cont derivativeLedgerNext stepLedgerNext banachLedgerNext ->
                          NewtonIterationCarrier derivativeSourceNext banachSourceNext
                              pointNext derivativeNext inverseRowNext nextStepNext
                              derivativeLedgerNext banachLedgerNext stepLedgerNext ∧
                            hsame derivativeLedger derivativeLedgerNext ∧
                              hsame stepLedger stepLedgerNext ∧
                                hsame nextStep nextStepNext ∧
                                  hsame banachLedger banachLedgerNext := by
  intro carrier sameDerivativeSource sameBanachSource samePoint sameDerivative sameInverseRow
    sourceRows derivativeRows stepRows nextRows banachRows
  have pointUnary : UnaryHistory pointNext :=
    unary_transport carrier.right.left samePoint
  have derivativeUnary : UnaryHistory derivativeNext :=
    unary_transport carrier.right.right.left sameDerivative
  have inverseRowUnary : UnaryHistory inverseRowNext :=
    unary_transport carrier.right.right.right.left sameInverseRow
  have stepLedgerUnary : UnaryHistory stepLedgerNext :=
    unary_cont_closed derivativeUnary inverseRowUnary stepRows
  have nextStepUnary : UnaryHistory nextStepNext :=
    unary_cont_closed pointUnary stepLedgerUnary nextRows
  have sameDerivativeLedger : hsame derivativeLedger derivativeLedgerNext :=
    cont_respects_hsame sameDerivativeSource sameBanachSource carrier.left sourceRows
  have sameStepLedger : hsame stepLedger stepLedgerNext :=
    cont_respects_hsame sameDerivative sameInverseRow
      carrier.right.right.right.right.right.right.left stepRows
  have sameNextStep : hsame nextStep nextStepNext :=
    cont_respects_hsame samePoint sameStepLedger
      carrier.right.right.right.right.right.right.right.left nextRows
  have sameBanachLedger : hsame banachLedger banachLedgerNext :=
    cont_respects_hsame sameDerivativeLedger sameStepLedger
      carrier.right.right.right.right.right.right.right.right banachRows
  exact
    And.intro
      (And.intro sourceRows
        (And.intro pointUnary
          (And.intro derivativeUnary
            (And.intro inverseRowUnary
              (And.intro nextStepUnary
                (And.intro derivativeRows
                  (And.intro stepRows
                    (And.intro nextRows banachRows))))))))
      (And.intro sameDerivativeLedger
        (And.intro sameStepLedger
          (And.intro sameNextStep sameBanachLedger)))

end BEDC.Derived.NewtonIterationUp
