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
