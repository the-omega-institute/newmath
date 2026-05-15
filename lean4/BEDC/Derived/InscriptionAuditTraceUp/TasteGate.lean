import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InscriptionAuditTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InscriptionAuditTraceUp : Type where
  | mk : (S M R K U Q H C P N : BHist) → InscriptionAuditTraceUp
  deriving DecidableEq

def inscriptionAuditTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscriptionAuditTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscriptionAuditTraceEncodeBHist h

def inscriptionAuditTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscriptionAuditTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscriptionAuditTraceDecodeBHist tail)

private theorem inscriptionAuditTraceDecode_encode_bhist :
    ∀ h : BHist,
      inscriptionAuditTraceDecodeBHist (inscriptionAuditTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def inscriptionAuditTraceToEventFlow : InscriptionAuditTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InscriptionAuditTraceUp.mk S M R K U Q H C P N =>
      [[BMark.b0],
        inscriptionAuditTraceEncodeBHist S,
        [BMark.b1, BMark.b0],
        inscriptionAuditTraceEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b0],
        inscriptionAuditTraceEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionAuditTraceEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionAuditTraceEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionAuditTraceEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionAuditTraceEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        inscriptionAuditTraceEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        inscriptionAuditTraceEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        inscriptionAuditTraceEncodeBHist N]

def inscriptionAuditTraceFromEventFlow : EventFlow → Option InscriptionAuditTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | K :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | U :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | Q :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (InscriptionAuditTraceUp.mk
                                                                                          (inscriptionAuditTraceDecodeBHist S)
                                                                                          (inscriptionAuditTraceDecodeBHist M)
                                                                                          (inscriptionAuditTraceDecodeBHist R)
                                                                                          (inscriptionAuditTraceDecodeBHist K)
                                                                                          (inscriptionAuditTraceDecodeBHist U)
                                                                                          (inscriptionAuditTraceDecodeBHist Q)
                                                                                          (inscriptionAuditTraceDecodeBHist H)
                                                                                          (inscriptionAuditTraceDecodeBHist C)
                                                                                          (inscriptionAuditTraceDecodeBHist P)
                                                                                          (inscriptionAuditTraceDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem inscriptionAuditTrace_round_trip :
    ∀ x : InscriptionAuditTraceUp,
      inscriptionAuditTraceFromEventFlow (inscriptionAuditTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M R K U Q H C P N =>
      change
        some
          (InscriptionAuditTraceUp.mk
            (inscriptionAuditTraceDecodeBHist (inscriptionAuditTraceEncodeBHist S))
            (inscriptionAuditTraceDecodeBHist (inscriptionAuditTraceEncodeBHist M))
            (inscriptionAuditTraceDecodeBHist (inscriptionAuditTraceEncodeBHist R))
            (inscriptionAuditTraceDecodeBHist (inscriptionAuditTraceEncodeBHist K))
            (inscriptionAuditTraceDecodeBHist (inscriptionAuditTraceEncodeBHist U))
            (inscriptionAuditTraceDecodeBHist (inscriptionAuditTraceEncodeBHist Q))
            (inscriptionAuditTraceDecodeBHist (inscriptionAuditTraceEncodeBHist H))
            (inscriptionAuditTraceDecodeBHist (inscriptionAuditTraceEncodeBHist C))
            (inscriptionAuditTraceDecodeBHist (inscriptionAuditTraceEncodeBHist P))
            (inscriptionAuditTraceDecodeBHist (inscriptionAuditTraceEncodeBHist N))) =
          some (InscriptionAuditTraceUp.mk S M R K U Q H C P N)
      rw [inscriptionAuditTraceDecode_encode_bhist S,
        inscriptionAuditTraceDecode_encode_bhist M,
        inscriptionAuditTraceDecode_encode_bhist R,
        inscriptionAuditTraceDecode_encode_bhist K,
        inscriptionAuditTraceDecode_encode_bhist U,
        inscriptionAuditTraceDecode_encode_bhist Q,
        inscriptionAuditTraceDecode_encode_bhist H,
        inscriptionAuditTraceDecode_encode_bhist C,
        inscriptionAuditTraceDecode_encode_bhist P,
        inscriptionAuditTraceDecode_encode_bhist N]

private theorem inscriptionAuditTraceToEventFlow_injective {x y : InscriptionAuditTraceUp} :
    inscriptionAuditTraceToEventFlow x = inscriptionAuditTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inscriptionAuditTraceFromEventFlow (inscriptionAuditTraceToEventFlow x) =
        inscriptionAuditTraceFromEventFlow (inscriptionAuditTraceToEventFlow y) :=
    congrArg inscriptionAuditTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (inscriptionAuditTrace_round_trip x).symm
      (Eq.trans hread (inscriptionAuditTrace_round_trip y)))

instance inscriptionAuditTraceBHistCarrier : BHistCarrier InscriptionAuditTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inscriptionAuditTraceToEventFlow
  fromEventFlow := inscriptionAuditTraceFromEventFlow

instance inscriptionAuditTraceChapterTasteGate :
    ChapterTasteGate InscriptionAuditTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change inscriptionAuditTraceFromEventFlow (inscriptionAuditTraceToEventFlow x) = some x
    exact inscriptionAuditTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscriptionAuditTraceToEventFlow_injective heq)

def inscriptionAuditTraceFields : InscriptionAuditTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | InscriptionAuditTraceUp.mk S M R K U Q H C P N =>
      [S, M, R, K, U, Q, H, C, P, N]

private theorem inscriptionAuditTrace_fields_faithful :
    ∀ x y : InscriptionAuditTraceUp,
      inscriptionAuditTraceFields x = inscriptionAuditTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S M R K U Q H C P N =>
      cases y with
      | mk S' M' R' K' U' Q' H' C' P' N' =>
          cases hfields
          rfl

instance inscriptionAuditTraceFieldFaithful :
    FieldFaithful InscriptionAuditTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := inscriptionAuditTraceFields
  field_faithful := inscriptionAuditTrace_fields_faithful

instance inscriptionAuditTraceNontrivial :
    Nontrivial InscriptionAuditTraceUp where
  witness_pair :=
    ⟨InscriptionAuditTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      InscriptionAuditTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate InscriptionAuditTraceUp :=
  inferInstance

theorem InscriptionAuditTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist, inscriptionAuditTraceDecodeBHist
        (inscriptionAuditTraceEncodeBHist h) = h) ∧
      (∀ x : InscriptionAuditTraceUp,
        inscriptionAuditTraceFromEventFlow (inscriptionAuditTraceToEventFlow x) = some x) ∧
        (∀ x y : InscriptionAuditTraceUp,
          inscriptionAuditTraceToEventFlow x = inscriptionAuditTraceToEventFlow y → x = y) ∧
          inscriptionAuditTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact inscriptionAuditTraceDecode_encode_bhist
  · constructor
    · exact inscriptionAuditTrace_round_trip
    · constructor
      · intro x y heq
        exact inscriptionAuditTraceToEventFlow_injective heq
      · rfl

end BEDC.Derived.InscriptionAuditTraceUp
