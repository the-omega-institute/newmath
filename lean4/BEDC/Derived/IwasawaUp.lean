import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.IwasawaUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

inductive IwasawaTransitionLedger : List BHist → BHist → Prop where
  | nil {provenance : BHist} :
      hsame provenance BHist.Empty → IwasawaTransitionLedger [] provenance
  | cons {level next transition provenance : BHist} {rest : List BHist} :
      UnaryHistory level →
        UnaryHistory next →
          Cont level next transition →
            IwasawaTransitionLedger rest provenance →
              IwasawaTransitionLedger (transition :: rest) provenance

theorem IwasawaTransitionLedger_finite_window_exactness
    {transitions : List BHist} {provenance row : BHist} :
    IwasawaTransitionLedger transitions provenance →
      List.Mem row transitions →
        ∃ level next : BHist, UnaryHistory level ∧ UnaryHistory next ∧ Cont level next row := by
  intro ledger rowMem
  induction ledger with
  | nil _ =>
      cases rowMem
  | cons levelUnary nextUnary transitionCont restLedger ih =>
      cases rowMem with
      | head =>
          exact Exists.intro _
            (Exists.intro _
              (And.intro levelUnary (And.intro nextUnary transitionCont)))
      | tail _ restMem =>
          exact ih restMem

private theorem IwasawaTransitionLedger_provenance_hsame_transport_aux
    {transitions : List BHist} {provenance provenance' : BHist} :
    IwasawaTransitionLedger transitions provenance ->
      hsame provenance provenance' ->
        IwasawaTransitionLedger transitions provenance' := by
  intro ledger sameProvenance
  induction ledger with
  | nil sameEmpty =>
      exact IwasawaTransitionLedger.nil (hsame_trans (hsame_symm sameProvenance) sameEmpty)
  | cons levelUnary nextUnary transitionCont _ ih =>
      exact IwasawaTransitionLedger.cons levelUnary nextUnary transitionCont
        (ih sameProvenance)

theorem IwasawaTransitionLedger_provenance_hsame_transport
    {transitions : List BHist} {provenance provenance' row : BHist} :
    IwasawaTransitionLedger transitions provenance ->
      hsame provenance provenance' ->
        List.Mem row transitions ->
          IwasawaTransitionLedger transitions provenance' ∧
            ∃ level next : BHist, UnaryHistory level ∧ UnaryHistory next ∧
              Cont level next row := by
  intro ledger sameProvenance rowMem
  have ledger' :=
    IwasawaTransitionLedger_provenance_hsame_transport_aux ledger sameProvenance
  have rowExact :=
    IwasawaTransitionLedger_finite_window_exactness ledger rowMem
  exact And.intro ledger' rowExact

theorem IwasawaTransitionLedger_cons_transport_stability
    {level level' next next' transition transition' provenance : BHist} {rest : List BHist} :
    UnaryHistory level -> UnaryHistory next -> hsame level level' -> hsame next next' ->
      Cont level next transition -> Cont level' next' transition' ->
        IwasawaTransitionLedger rest provenance ->
          IwasawaTransitionLedger (transition' :: rest) provenance ∧ hsame transition transition' ∧
            UnaryHistory transition' := by
  intro levelUnary nextUnary sameLevel sameNext transitionCont transitionCont' restLedger
  have levelUnary' : UnaryHistory level' :=
    unary_transport levelUnary sameLevel
  have nextUnary' : UnaryHistory next' :=
    unary_transport nextUnary sameNext
  have sameTransition : hsame transition transition' :=
    cont_respects_hsame sameLevel sameNext transitionCont transitionCont'
  have transitionUnary' : UnaryHistory transition' :=
    unary_cont_closed levelUnary' nextUnary' transitionCont'
  exact
    And.intro
      (IwasawaTransitionLedger.cons levelUnary' nextUnary' transitionCont' restLedger)
      (And.intro sameTransition transitionUnary')

theorem IwasawaTransitionLedger_transition_hsame_transport
    {transitions : List BHist} {provenance row row' : BHist} :
    IwasawaTransitionLedger transitions provenance ->
      List.Mem row transitions ->
        hsame row row' ->
          ∃ level next : BHist, UnaryHistory level ∧ UnaryHistory next ∧
            Cont level next row' := by
  intro ledger rowMem sameRow
  have exactRow :=
    IwasawaTransitionLedger_finite_window_exactness ledger rowMem
  cases exactRow with
  | intro level exactRest =>
      cases exactRest with
      | intro next rowData =>
          exact Exists.intro level
              (Exists.intro next
                (And.intro rowData.left
                  (And.intro rowData.right.left
                    (cont_result_hsame_transport rowData.right.right sameRow))))

end BEDC.Derived.IwasawaUp
