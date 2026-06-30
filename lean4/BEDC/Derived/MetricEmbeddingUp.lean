import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricEmbeddingUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def MetricEmbeddingCarrier (X Y F D R S H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory F ∧ UnaryHistory D ∧
    UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont X F D ∧ Cont D R S ∧ Cont H C P

theorem MetricEmbeddingCarrier_surface
    {X Y F D R S H C P N : BHist} :
    MetricEmbeddingCarrier X Y F D R S H C P N ->
      UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory P ∧
        Cont X F D ∧ Cont D R S ∧ Cont H C P := by
  -- BEDC touchpoint anchor: MetricEmbeddingCarrier BHist Cont UnaryHistory
  intro carrier
  obtain ⟨xUnary, _yUnary, fUnary, _dUnary, rUnary, _sUnary, hUnary, cUnary,
    _pUnary, _nUnary, graphRoute, separatedRoute, provenanceRoute⟩ := carrier
  have dClosed : UnaryHistory D :=
    unary_cont_closed xUnary fUnary graphRoute
  have sClosed : UnaryHistory S :=
    unary_cont_closed dClosed rUnary separatedRoute
  have pClosed : UnaryHistory P :=
    unary_cont_closed hUnary cUnary provenanceRoute
  exact ⟨dClosed, sClosed, pClosed, graphRoute, separatedRoute, provenanceRoute⟩

end BEDC.Derived.MetricEmbeddingUp
