import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BeliefUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def BeliefObservationUpdateCarrier
    (prior observation trace probability ledger posterior : BHist) : Prop :=
  UnaryHistory prior ∧ UnaryHistory observation ∧ UnaryHistory probability ∧
    Cont prior observation trace ∧ Cont trace probability posterior ∧
      Cont prior posterior ledger

theorem BeliefObservationUpdateCarrier_transport_obligation
    {prior observation trace probability ledger posterior prior' observation' trace' probability'
      ledger' posterior' : BHist} :
    BeliefObservationUpdateCarrier prior observation trace probability ledger posterior ->
      hsame prior' prior -> hsame observation' observation -> hsame probability' probability ->
        Cont prior' observation' trace' -> Cont trace' probability' posterior' ->
          Cont prior' posterior' ledger' ->
            BeliefObservationUpdateCarrier prior' observation' trace' probability' ledger'
                posterior' ∧
              hsame trace trace' ∧ hsame posterior posterior' ∧ hsame ledger ledger' := by
  intro carrier samePrior' sameObservation' sameProbability' traceRow' posteriorRow' ledgerRow'
  have priorUnary' : UnaryHistory prior' :=
    unary_transport carrier.left (hsame_symm samePrior')
  have observationUnary' : UnaryHistory observation' :=
    unary_transport carrier.right.left (hsame_symm sameObservation')
  have probabilityUnary' : UnaryHistory probability' :=
    unary_transport carrier.right.right.left (hsame_symm sameProbability')
  have sameTrace : hsame trace trace' :=
    cont_respects_hsame (hsame_symm samePrior') (hsame_symm sameObservation')
      carrier.right.right.right.left traceRow'
  have samePosterior : hsame posterior posterior' :=
    cont_respects_hsame sameTrace (hsame_symm sameProbability')
      carrier.right.right.right.right.left posteriorRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame (hsame_symm samePrior') samePosterior
      carrier.right.right.right.right.right ledgerRow'
  exact
    ⟨⟨priorUnary', observationUnary', probabilityUnary', traceRow', posteriorRow', ledgerRow'⟩,
      sameTrace, samePosterior, sameLedger⟩

theorem BeliefObservationUpdateCarrier_ledger_exactness
    {prior observation trace probability ledger posterior : BHist} :
    BeliefObservationUpdateCarrier prior observation trace probability ledger posterior ->
      UnaryHistory ledger ∧ hsame ledger (append prior posterior) ∧
        hsame trace (append prior observation) ∧
          hsame posterior (append trace probability) := by
  intro carrier
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed carrier.left carrier.right.left carrier.right.right.right.left
  have posteriorUnary : UnaryHistory posterior :=
    unary_cont_closed traceUnary carrier.right.right.left
      carrier.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrier.left posteriorUnary carrier.right.right.right.right.right
  exact
    ⟨ledgerUnary, carrier.right.right.right.right.right, carrier.right.right.right.left,
      carrier.right.right.right.right.left⟩

end BEDC.Derived.BeliefUp
