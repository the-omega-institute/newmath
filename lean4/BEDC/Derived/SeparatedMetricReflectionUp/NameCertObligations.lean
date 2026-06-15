import BEDC.Derived.SeparatedMetricReflectionUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SeparatedMetricReflectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem SeparatedMetricReflectionCarrier_namecert_obligations
    {x s a u z h c p n : BHist} (metricSeparatedRoute : Cont x s a)
    (adjunctionUniversalRoute : Cont a u z) (transportReplayRoute : Cont h c p)
    (sourceUnary : UnaryHistory x) (separatedUnary : UnaryHistory s)
    (universalUnary : UnaryHistory u) (transportUnary : UnaryHistory h)
    (replayUnary : UnaryHistory c) :
    UnaryHistory a ∧ UnaryHistory z ∧ UnaryHistory p ∧ hsame n n := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  have adjunctionUnary : UnaryHistory a :=
    unary_cont_closed sourceUnary separatedUnary metricSeparatedRoute
  have reflectedUnary : UnaryHistory z :=
    unary_cont_closed adjunctionUnary universalUnary adjunctionUniversalRoute
  have provenanceUnary : UnaryHistory p :=
    unary_cont_closed transportUnary replayUnary transportReplayRoute
  exact ⟨adjunctionUnary, reflectedUnary, provenanceUnary, hsame_refl n⟩

end BEDC.Derived.SeparatedMetricReflectionUp
