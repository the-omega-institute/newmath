import BEDC.FKernel.NameCert
import BEDC.Derived.SocketUseLedgerUp.TasteGate

namespace BEDC.Derived.SocketUseLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

private theorem SocketUseLedgerCarrier_public_event_surface_encode_decode_aux :
    ∀ event : List BMark, socketUseLedgerEncodeBHist (socketUseLedgerDecodeBHist event) = event := by
  -- BEDC touchpoint anchor: BHist BMark
  intro event
  induction event with
  | nil =>
      rfl
  | cons mark tail ih =>
      cases mark with
      | b0 =>
          exact congrArg (fun rest => BMark.b0 :: rest) ih
      | b1 =>
          exact congrArg (fun rest => BMark.b1 :: rest) ih

theorem SocketUseLedgerCarrier_visible_refusal_layer_separation :
    (∀ x : SocketUseLedgerUp,
      ∃ A S Q V R H C P N : BHist,
        x = SocketUseLedgerUp.mk A S Q V R H C P N ∧
          FieldFaithful.fields x = [A, S, Q, V, R, H, C, P, N]) ∧
      (∀ A S Q H C P N : BHist,
        BHistCarrier.toEventFlow
          (SocketUseLedgerUp.mk A S Q (BHist.e0 BHist.Empty) BHist.Empty H C P N) ≠
        BHistCarrier.toEventFlow
          (SocketUseLedgerUp.mk A S Q BHist.Empty (BHist.e0 BHist.Empty) H C P N)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    cases x with
    | mk A S Q V R H C P N =>
        exact ⟨A, S, Q, V, R, H, C, P, N, rfl, rfl⟩
  · intro A S Q H C P N heq
    change
      socketUseLedgerToEventFlow
          (SocketUseLedgerUp.mk A S Q (BHist.e0 BHist.Empty) BHist.Empty H C P N) =
        socketUseLedgerToEventFlow
          (SocketUseLedgerUp.mk A S Q BHist.Empty (BHist.e0 BHist.Empty) H C P N) at heq
    injection heq with _ htail₁
    injection htail₁ with _ htail₂
    injection htail₂ with _ htail₃
    injection htail₃ with hrow _
    cases hrow

theorem SocketUseLedgerCarrier_namecert_obligations (x : SocketUseLedgerUp) :
    SemanticNameCert
        (fun row : BHist => row ∈ socketUseLedgerFields x)
        (fun row : BHist => row ∈ socketUseLedgerFields x)
        (fun row : BHist => row ∈ socketUseLedgerFields x)
        hsame ∧
      socketUseLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark SemanticNameCert hsame NameCert
  cases x with
  | mk A S Q V R H C P N =>
      constructor
      · exact
          { core :=
              { carrier_inhabited := ⟨A, List.Mem.head _⟩
                equiv_refl := by
                  intro row _rowMember
                  exact hsame_refl row
                equiv_symm := by
                  intro row row' sameRows
                  exact hsame_symm sameRows
                equiv_trans := by
                  intro row row' row'' sameLeft sameRight
                  exact hsame_trans sameLeft sameRight
                carrier_respects_equiv := by
                  intro row row' sameRows rowMember
                  cases sameRows
                  exact rowMember }
            pattern_sound := by
              intro _row rowMember
              exact rowMember
            ledger_sound := by
              intro _row rowMember
              exact rowMember }
      · rfl

theorem SocketUseLedgerCarrier_public_event_surface :
    (∀ event : List BMark,
        socketUseLedgerEncodeBHist (socketUseLedgerDecodeBHist event) = event) ∧
      (∀ ef x,
        socketUseLedgerFromEventFlow ef = some x →
          socketUseLedgerToEventFlow x = ef) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SocketUseLedgerCarrier_public_event_surface_encode_decode_aux
  · intro ef x hread
    cases ef with
    | nil =>
        cases hread
    | cons A rest0 =>
        cases rest0 with
        | nil =>
            cases hread
        | cons S rest1 =>
            cases rest1 with
            | nil =>
                cases hread
            | cons Q rest2 =>
                cases rest2 with
                | nil =>
                    cases hread
                | cons V rest3 =>
                    cases rest3 with
                    | nil =>
                        cases hread
                    | cons R rest4 =>
                        cases rest4 with
                        | nil =>
                            cases hread
                        | cons H rest5 =>
                            cases rest5 with
                            | nil =>
                                cases hread
                            | cons C rest6 =>
                                cases rest6 with
                                | nil =>
                                    cases hread
                                | cons P rest7 =>
                                    cases rest7 with
                                    | nil =>
                                        cases hread
                                    | cons N rest8 =>
                                        cases rest8 with
                                        | nil =>
                                            cases hread
                                            change
                                              [socketUseLedgerEncodeBHist
                                                  (socketUseLedgerDecodeBHist A),
                                                socketUseLedgerEncodeBHist
                                                  (socketUseLedgerDecodeBHist S),
                                                socketUseLedgerEncodeBHist
                                                  (socketUseLedgerDecodeBHist Q),
                                                socketUseLedgerEncodeBHist
                                                  (socketUseLedgerDecodeBHist V),
                                                socketUseLedgerEncodeBHist
                                                  (socketUseLedgerDecodeBHist R),
                                                socketUseLedgerEncodeBHist
                                                  (socketUseLedgerDecodeBHist H),
                                                socketUseLedgerEncodeBHist
                                                  (socketUseLedgerDecodeBHist C),
                                                socketUseLedgerEncodeBHist
                                                  (socketUseLedgerDecodeBHist P),
                                                socketUseLedgerEncodeBHist
                                                  (socketUseLedgerDecodeBHist N)] =
                                                [A, S, Q, V, R, H, C, P, N]
                                            rw [
                                              SocketUseLedgerCarrier_public_event_surface_encode_decode_aux A,
                                              SocketUseLedgerCarrier_public_event_surface_encode_decode_aux S,
                                              SocketUseLedgerCarrier_public_event_surface_encode_decode_aux Q,
                                              SocketUseLedgerCarrier_public_event_surface_encode_decode_aux V,
                                              SocketUseLedgerCarrier_public_event_surface_encode_decode_aux R,
                                              SocketUseLedgerCarrier_public_event_surface_encode_decode_aux H,
                                              SocketUseLedgerCarrier_public_event_surface_encode_decode_aux C,
                                              SocketUseLedgerCarrier_public_event_surface_encode_decode_aux P,
                                              SocketUseLedgerCarrier_public_event_surface_encode_decode_aux N]
                                        | cons extra extraRest =>
                                            cases hread

end BEDC.Derived.SocketUseLedgerUp
