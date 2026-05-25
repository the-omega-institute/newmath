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

theorem CauchySpaceCarrier_uniform_regseq_interface {F U R Q T H C P N replay : BHist} :
    CauchySpaceCarrier F U R Q T H C P N ->
      Cont F U replay ->
        UnaryHistory F ∧ UnaryHistory U ∧ UnaryHistory R ∧ UnaryHistory replay ∧
          hsame replay R ∧ hsame H (append F U) := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro carrier replayRoute
  obtain ⟨fUnary, uUnary, rUnary, _qUnary, _tUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    transportRow, filterRoute, _nameRoute⟩ := carrier
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed fUnary uUnary replayRoute
  have replaySame : hsame replay R :=
    cont_deterministic replayRoute filterRoute
  exact ⟨fUnary, uUnary, rUnary, replayUnary, replaySame, transportRow⟩

theorem CauchySpaceCarrier_filter_uniform_compatibility
    {F U R Q T H C P N filterUniform replay named : BHist} :
    CauchySpaceCarrier F U R Q T H C P N ->
      Cont F U filterUniform ->
        Cont filterUniform C replay ->
          Cont replay P named ->
            UnaryHistory F ∧ UnaryHistory U ∧ UnaryHistory filterUniform ∧
              UnaryHistory replay ∧ UnaryHistory named ∧ hsame H (append F U) ∧
                Cont F U filterUniform ∧ Cont filterUniform C replay ∧
                  Cont replay P named := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro carrier filterUniformRoute replayRoute namedRoute
  obtain ⟨fUnary, uUnary, _rUnary, _qUnary, _tUnary, _hUnary, cUnary, pUnary,
    _nUnary, transportRow, _filterRoute, _nameRoute⟩ := carrier
  have filterUniformUnary : UnaryHistory filterUniform :=
    unary_cont_closed fUnary uUnary filterUniformRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed filterUniformUnary cUnary replayRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed replayUnary pUnary namedRoute
  exact
    ⟨fUnary, uUnary, filterUniformUnary, replayUnary, namedUnary, transportRow,
      filterUniformRoute, replayRoute, namedRoute⟩

theorem CauchySpaceCarrier_real_completion_consumer {F U R Q T H C P N replay realRead : BHist} :
    CauchySpaceCarrier F U R Q T H C P N ->
      Cont F U replay ->
        Cont replay N realRead ->
          UnaryHistory F ∧ UnaryHistory U ∧ UnaryHistory R ∧ UnaryHistory replay ∧
            UnaryHistory N ∧ UnaryHistory realRead ∧ hsame replay R ∧
              hsame H (append F U) ∧ Cont F U replay ∧ Cont replay N realRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro carrier replayRoute realReadRoute
  have interface :=
    CauchySpaceCarrier_uniform_regseq_interface
      (F := F) (U := U) (R := R) (Q := Q) (T := T) (H := H) (C := C)
      (P := P) (N := N) (replay := replay) carrier replayRoute
  obtain ⟨fUnary, uUnary, rUnary, replayUnary, replaySame, transportRow⟩ := interface
  obtain ⟨_fUnary, _uUnary, _rUnary, _qUnary, _tUnary, _hUnary, _cUnary, _pUnary,
    nUnary, _transportRow, _filterRoute, _nameRoute⟩ := carrier
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed replayUnary nUnary realReadRoute
  exact
    ⟨fUnary, uUnary, rUnary, replayUnary, nUnary, realReadUnary, replaySame,
      transportRow, replayRoute, realReadRoute⟩

end BEDC.Derived.CauchySpaceUp
