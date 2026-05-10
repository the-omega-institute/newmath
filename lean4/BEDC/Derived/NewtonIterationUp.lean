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

end BEDC.Derived.NewtonIterationUp
