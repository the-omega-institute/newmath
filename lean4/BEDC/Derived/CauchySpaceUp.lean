import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchySpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def CauchySpaceCarrier (F U R Q T H C P N : BHist) : Prop :=
  UnaryHistory F ∧ UnaryHistory U ∧ UnaryHistory R ∧ UnaryHistory Q ∧
    UnaryHistory T ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ hsame H (append F U) ∧ Cont F U R ∧ Cont C P N

theorem CauchySpaceCarrier_filter_stability {F U R Q T H C P N replay : BHist} :
    CauchySpaceCarrier F U R Q T H C P N ->
      Cont F U replay -> UnaryHistory F ∧ UnaryHistory replay ∧ hsame H (append F U) := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro carrier replayRoute
  obtain ⟨fUnary, uUnary, _rUnary, _qUnary, _tUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    transportRow, _filterRoute, _nameRoute⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed fUnary uUnary replayRoute
  exact ⟨fUnary, replayUnary, transportRow⟩

end BEDC.Derived.CauchySpaceUp
