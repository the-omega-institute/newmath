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

theorem CauchySpaceCarrier_filter_uniform_real_consumer_obligation
    {F U R Q T H C P N filterUniform replay realRead : BHist} :
    CauchySpaceCarrier F U R Q T H C P N ->
      Cont F U filterUniform ->
        Cont filterUniform C replay ->
          Cont replay N realRead ->
            UnaryHistory F ∧ UnaryHistory U ∧ UnaryHistory R ∧
              UnaryHistory filterUniform ∧ UnaryHistory replay ∧ UnaryHistory N ∧
                UnaryHistory realRead ∧ hsame H (append F U) ∧ Cont F U filterUniform ∧
                  Cont filterUniform C replay ∧ Cont replay N realRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro carrier filterUniformRoute replayRoute realReadRoute
  obtain ⟨fUnary, uUnary, rUnary, _qUnary, _tUnary, _hUnary, cUnary, _pUnary,
    nUnary, transportRow, _carrierFilterRoute, _carrierNameRoute⟩ := carrier
  have filterUniformUnary : UnaryHistory filterUniform :=
    unary_cont_closed fUnary uUnary filterUniformRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed filterUniformUnary cUnary replayRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed replayUnary nUnary realReadRoute
  exact
    ⟨fUnary, uUnary, rUnary, filterUniformUnary, replayUnary, nUnary, realReadUnary,
      transportRow, filterUniformRoute, replayRoute, realReadRoute⟩

theorem CauchySpaceCarrier_regseqrat_uniform_obligation
    {F0 F1 U0 R0 T0 H0 C0 P0 N0 replay named : BHist} :
    CauchySpaceCarrier F0 U0 R0 F1 T0 H0 C0 P0 N0 ->
      Cont F0 U0 replay ->
        Cont replay P0 named ->
          UnaryHistory F0 ∧ UnaryHistory U0 ∧ UnaryHistory R0 ∧
            UnaryHistory replay ∧ UnaryHistory named ∧ hsame replay R0 ∧
              hsame H0 (append F0 U0) ∧ Cont F0 U0 replay ∧
                Cont replay P0 named := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro carrier replayRoute namedRoute
  have interface :=
    CauchySpaceCarrier_uniform_regseq_interface
      (F := F0) (U := U0) (R := R0) (Q := F1) (T := T0) (H := H0)
      (C := C0) (P := P0) (N := N0) (replay := replay) carrier replayRoute
  obtain ⟨fUnary, uUnary, rUnary, replayUnary, replaySame, transportRow⟩ := interface
  obtain ⟨_fUnary, _uUnary, _rUnary, _qUnary, _tUnary, _hUnary, _cUnary, pUnary,
    _nUnary, _transportRow, _filterRoute, _nameRoute⟩ := carrier
  have namedUnary : UnaryHistory named :=
    unary_cont_closed replayUnary pUnary namedRoute
  exact
    ⟨fUnary, uUnary, rUnary, replayUnary, namedUnary, replaySame, transportRow,
      replayRoute, namedRoute⟩

theorem CauchySpaceCarrier_completion_handoff_obligation
    {F0 F1 U0 R0 T0 H0 C0 P0 N0 consumer : BHist} :
    CauchySpaceCarrier F0 U0 R0 F1 T0 H0 C0 P0 N0 ->
      Cont F0 U0 R0 ->
        Cont R0 T0 consumer ->
          UnaryHistory F0 ∧ UnaryHistory U0 ∧ UnaryHistory R0 ∧ UnaryHistory T0 ∧
            UnaryHistory consumer ∧ hsame H0 (append F0 U0) ∧ Cont F0 U0 R0 ∧
              Cont R0 T0 consumer := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro carrier filterRoute consumerRoute
  obtain ⟨fUnary, uUnary, rUnary, _qUnary, tUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    transportRow, _carrierFilterRoute, _carrierNameRoute⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed rUnary tUnary consumerRoute
  exact
    ⟨fUnary, uUnary, rUnary, tUnary, consumerUnary, transportRow, filterRoute,
      consumerRoute⟩

theorem CauchySpaceCarrier_precompletion_nonescape_obligation
    {F U R Q T H C P N handoff consumer : BHist} :
    CauchySpaceCarrier F U R Q T H C P N ->
      Cont R Q handoff ->
        Cont handoff T consumer ->
          UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory T ∧ UnaryHistory handoff ∧
            UnaryHistory consumer ∧ Cont R Q handoff ∧ Cont handoff T consumer ∧
              hsame H (append F U) := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro carrier handoffRoute consumerRoute
  obtain ⟨_fUnary, _uUnary, rUnary, qUnary, tUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, transportRow, _filterRoute, _nameRoute⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed rUnary qUnary handoffRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary tUnary consumerRoute
  exact
    ⟨rUnary, qUnary, tUnary, handoffUnary, consumerUnary, handoffRoute, consumerRoute,
      transportRow⟩

theorem CauchySpaceCarrier_regular_name_handoff_obligation
    {F U R Q T H C P N handoff named : BHist} :
    CauchySpaceCarrier F U R Q T H C P N ->
      Cont R Q handoff ->
        Cont handoff N named ->
          UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory N ∧ UnaryHistory handoff ∧
            UnaryHistory named ∧ Cont R Q handoff ∧ Cont handoff N named ∧
              hsame H (append F U) := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro carrier handoffRoute namedRoute
  obtain ⟨_fUnary, _uUnary, rUnary, qUnary, _tUnary, _hUnary, _cUnary, _pUnary,
    nUnary, transportRow, _filterRoute, _nameRoute⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed rUnary qUnary handoffRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed handoffUnary nUnary namedRoute
  exact
    ⟨rUnary, qUnary, nUnary, handoffUnary, namedUnary, handoffRoute, namedRoute,
      transportRow⟩

theorem CauchySpaceCarrier_filter_uniform_completion_nonescape
    {F0 F1 U0 R0 T0 H0 C0 P0 N0 replay consumer named : BHist} :
    CauchySpaceCarrier F0 U0 R0 F1 T0 H0 C0 P0 N0 ->
      Cont F0 U0 replay ->
        Cont replay T0 consumer ->
          Cont consumer P0 named ->
            UnaryHistory F0 ∧ UnaryHistory U0 ∧ UnaryHistory R0 ∧ UnaryHistory T0 ∧
              UnaryHistory replay ∧ UnaryHistory consumer ∧ UnaryHistory named ∧
                hsame replay R0 ∧ hsame H0 (append F0 U0) ∧ Cont F0 U0 replay ∧
                  Cont replay T0 consumer ∧ Cont consumer P0 named := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  intro carrier replayRoute consumerRoute namedRoute
  have interface :=
    CauchySpaceCarrier_uniform_regseq_interface
      (F := F0) (U := U0) (R := R0) (Q := F1) (T := T0) (H := H0)
      (C := C0) (P := P0) (N := N0) (replay := replay) carrier replayRoute
  obtain ⟨fUnary, uUnary, rUnary, replayUnary, replaySame, transportRow⟩ := interface
  obtain ⟨_fUnary, _uUnary, _rUnary, _qUnary, tUnary, _hUnary, _cUnary, pUnary,
    _nUnary, _transportRow, _filterRoute, _nameRoute⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed replayUnary tUnary consumerRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed consumerUnary pUnary namedRoute
  exact
    ⟨fUnary, uUnary, rUnary, tUnary, replayUnary, consumerUnary, namedUnary,
      replaySame, transportRow, replayRoute, consumerRoute, namedRoute⟩

end BEDC.Derived.CauchySpaceUp
