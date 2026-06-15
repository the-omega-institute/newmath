import BEDC.Derived.NonAxiomAdmissionUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NonAxiomAdmissionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem NonAxiomAdmissionCarrier_witness_route_nonescape
    {x f w h c p n consumerRead : BHist} (proposalWitnessRoute : Cont x f w)
    (transportReplayRoute : Cont h c p) (witnessConsumerRoute : Cont w n consumerRead)
    (proposalUnary : UnaryHistory x) (formUnary : UnaryHistory f)
    (transportUnary : UnaryHistory h) (replayUnary : UnaryHistory c)
    (localNameUnary : UnaryHistory n) :
    UnaryHistory w ∧ UnaryHistory p ∧ UnaryHistory consumerRead ∧
      hsame consumerRead consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory FieldFaithful
  have witnessUnary : UnaryHistory w :=
    unary_cont_closed proposalUnary formUnary proposalWitnessRoute
  have provenanceUnary : UnaryHistory p :=
    unary_cont_closed transportUnary replayUnary transportReplayRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed witnessUnary localNameUnary witnessConsumerRoute
  exact ⟨witnessUnary, provenanceUnary, consumerUnary, hsame_refl consumerRead⟩

end BEDC.Derived.NonAxiomAdmissionUp
