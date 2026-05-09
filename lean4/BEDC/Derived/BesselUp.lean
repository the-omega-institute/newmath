import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BesselUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def BesselRootPacket
    (ode holo order solution target recurrence transport provenance : BHist) : Prop :=
  UnaryHistory ode ∧ UnaryHistory holo ∧ UnaryHistory order ∧ UnaryHistory target ∧
    Cont ode order solution ∧ Cont solution target recurrence ∧
      hsame transport BHist.Empty ∧ Cont recurrence transport provenance

theorem BesselRootPacket_ode_source_obligation
    {ode holo order solution target recurrence transport provenance : BHist} :
    BesselRootPacket ode holo order solution target recurrence transport provenance ->
      UnaryHistory ode ∧ UnaryHistory order ∧ UnaryHistory solution ∧
        UnaryHistory recurrence ∧ UnaryHistory provenance ∧ Cont ode order solution ∧
          hsame transport BHist.Empty := by
  intro packet
  have solutionUnary : UnaryHistory solution :=
    unary_cont_closed packet.left packet.right.right.left packet.right.right.right.right.left
  have recurrenceUnary : UnaryHistory recurrence :=
    unary_cont_closed solutionUnary packet.right.right.right.left
      packet.right.right.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    unary_transport unary_empty (hsame_symm packet.right.right.right.right.right.right.left)
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed recurrenceUnary transportUnary packet.right.right.right.right.right.right.right
  exact And.intro packet.left
    (And.intro packet.right.right.left
      (And.intro solutionUnary
        (And.intro recurrenceUnary
          (And.intro provenanceUnary
            (And.intro packet.right.right.right.right.left
              packet.right.right.right.right.right.right.left)))))

end BEDC.Derived.BesselUp
