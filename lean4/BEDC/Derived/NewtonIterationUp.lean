import BEDC.FKernel.Cont
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

end BEDC.Derived.NewtonIterationUp
