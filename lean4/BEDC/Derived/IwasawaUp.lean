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

end BEDC.Derived.IwasawaUp
