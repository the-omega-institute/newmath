import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeriesLimitComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeriesLimitComparisonUp : Type where
  | mk (A B S T R D W Q E H C P N : BHist) : SeriesLimitComparisonUp
  deriving DecidableEq

def seriesLimitComparisonEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: seriesLimitComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: seriesLimitComparisonEncodeBHist h

def seriesLimitComparisonDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (seriesLimitComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (seriesLimitComparisonDecodeBHist tail)

private theorem SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def seriesLimitComparisonFields : SeriesLimitComparisonUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SeriesLimitComparisonUp.mk A B S T R D W Q E H C P N =>
      [A, B, S, T, R, D, W, Q, E, H, C, P, N]

def seriesLimitComparisonToEventFlow : SeriesLimitComparisonUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (seriesLimitComparisonFields x).map seriesLimitComparisonEncodeBHist

def seriesLimitComparisonFromEventFlow : EventFlow -> Option SeriesLimitComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | A :: rest0 =>
      match rest0 with
      | [] => none
      | B :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D :: rest5 =>
                          match rest5 with
                          | [] => none
                          | W :: rest6 =>
                              match rest6 with
                              | [] => none
                              | Q :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | E :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | C :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | P :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | N :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (SeriesLimitComparisonUp.mk
                                                              (seriesLimitComparisonDecodeBHist A)
                                                              (seriesLimitComparisonDecodeBHist B)
                                                              (seriesLimitComparisonDecodeBHist S)
                                                              (seriesLimitComparisonDecodeBHist T)
                                                              (seriesLimitComparisonDecodeBHist R)
                                                              (seriesLimitComparisonDecodeBHist D)
                                                              (seriesLimitComparisonDecodeBHist W)
                                                              (seriesLimitComparisonDecodeBHist Q)
                                                              (seriesLimitComparisonDecodeBHist E)
                                                              (seriesLimitComparisonDecodeBHist H)
                                                              (seriesLimitComparisonDecodeBHist C)
                                                              (seriesLimitComparisonDecodeBHist P)
                                                              (seriesLimitComparisonDecodeBHist N))
                                                      | _ :: _ => none

private theorem SeriesLimitComparisonUpTasteGate_single_carrier_alignment_round_trip :
    forall x : SeriesLimitComparisonUp,
      seriesLimitComparisonFromEventFlow (seriesLimitComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B S T R D W Q E H C P N =>
      change
        some
          (SeriesLimitComparisonUp.mk
            (seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist A))
            (seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist B))
            (seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist S))
            (seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist T))
            (seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist R))
            (seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist D))
            (seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist W))
            (seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist Q))
            (seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist E))
            (seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist H))
            (seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist C))
            (seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist P))
            (seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist N))) =
          some (SeriesLimitComparisonUp.mk A B S T R D W Q E H C P N)
      rw [SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode A,
        SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode B,
        SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode S,
        SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode T,
        SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode R,
        SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode D,
        SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode W,
        SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode Q,
        SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode E,
        SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode H,
        SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode C,
        SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode P,
        SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem SeriesLimitComparisonUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SeriesLimitComparisonUp} :
    seriesLimitComparisonToEventFlow x = seriesLimitComparisonToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      seriesLimitComparisonFromEventFlow (seriesLimitComparisonToEventFlow x) =
        seriesLimitComparisonFromEventFlow (seriesLimitComparisonToEventFlow y) :=
    congrArg seriesLimitComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SeriesLimitComparisonUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SeriesLimitComparisonUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem SeriesLimitComparisonUpTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : SeriesLimitComparisonUp,
      seriesLimitComparisonFields x = seriesLimitComparisonFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 B1 S1 T1 R1 D1 W1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 B2 S2 T2 R2 D2 W2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance seriesLimitComparisonBHistCarrier : BHistCarrier SeriesLimitComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := seriesLimitComparisonToEventFlow
  fromEventFlow := seriesLimitComparisonFromEventFlow

instance seriesLimitComparisonChapterTasteGate : ChapterTasteGate SeriesLimitComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change seriesLimitComparisonFromEventFlow (seriesLimitComparisonToEventFlow x) = some x
    exact SeriesLimitComparisonUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SeriesLimitComparisonUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance seriesLimitComparisonFieldFaithful : FieldFaithful SeriesLimitComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := seriesLimitComparisonFields
  field_faithful := SeriesLimitComparisonUpTasteGate_single_carrier_alignment_fields_faithful

instance seriesLimitComparisonNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SeriesLimitComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SeriesLimitComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      SeriesLimitComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def seriesLimitComparisonTasteGate : ChapterTasteGate SeriesLimitComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  seriesLimitComparisonChapterTasteGate

theorem SeriesLimitComparisonUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SeriesLimitComparisonUp) ∧
      Nonempty (FieldFaithful SeriesLimitComparisonUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial SeriesLimitComparisonUp) ∧
          (∀ h : BHist,
            seriesLimitComparisonDecodeBHist (seriesLimitComparisonEncodeBHist h) = h) ∧
            (∀ x : SeriesLimitComparisonUp,
              seriesLimitComparisonFromEventFlow (seriesLimitComparisonToEventFlow x) = some x) ∧
              (∀ x y : SeriesLimitComparisonUp,
                seriesLimitComparisonToEventFlow x = seriesLimitComparisonToEventFlow y -> x = y) ∧
                seriesLimitComparisonEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨seriesLimitComparisonChapterTasteGate⟩
  · constructor
    · exact ⟨seriesLimitComparisonFieldFaithful⟩
    · constructor
      · exact ⟨seriesLimitComparisonNontrivial⟩
      · constructor
        · exact SeriesLimitComparisonUpTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact SeriesLimitComparisonUpTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact SeriesLimitComparisonUpTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.SeriesLimitComparisonUp
