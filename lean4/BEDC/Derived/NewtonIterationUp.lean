import BEDC.FKernel.Cont
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NewtonIterationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.NewtonIterationUp
