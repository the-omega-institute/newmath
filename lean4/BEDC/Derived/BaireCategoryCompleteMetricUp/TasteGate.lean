import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireCategoryCompleteMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireCategoryCompleteMetricUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (B K M D S R Y E H C P N : BHist) : BaireCategoryCompleteMetricUp
  deriving DecidableEq

def BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist h

def BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fields :
    BaireCategoryCompleteMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireCategoryCompleteMetricUp.mk B K M D S R Y E H C P N =>
      [B, K, M, D, S, R, Y, E, H, C, P, N]

def BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow :
    BaireCategoryCompleteMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fields x).map
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist

private def BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt index rest

def BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option BaireCategoryCompleteMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireCategoryCompleteMetricUp.mk
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 0 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 1 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 2 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 3 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 4 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 5 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 6 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 7 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 8 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 9 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 10 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 11 ef)))

private theorem BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_round_trip
    (x : BaireCategoryCompleteMetricUp) :
    BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B K M D S R Y E H C P N =>
      change
        some
          (BaireCategoryCompleteMetricUp.mk
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist B))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist K))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist M))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist D))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist S))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist R))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist Y))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist E))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist H))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist C))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist P))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (BaireCategoryCompleteMetricUp.mk B K M D S R Y E H C P N)
      rw [BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode B,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode K,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode M,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode D,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode S,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode R,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode Y,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode E,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode H,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode C,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode P,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode N]

private theorem BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_injective
    {x y : BaireCategoryCompleteMetricUp} :
    BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow x =
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow
          (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow x) =
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow
          (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : BaireCategoryCompleteMetricUp,
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fields x =
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 K1 M1 D1 S1 R1 Y1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 K2 M2 D2 S2 R2 Y2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance baireCategoryCompleteMetricBHistCarrier :
    BHistCarrier BaireCategoryCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow

instance baireCategoryCompleteMetricChapterTasteGate :
    ChapterTasteGate BaireCategoryCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_injective heq)

instance baireCategoryCompleteMetricFieldFaithful :
    FieldFaithful BaireCategoryCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fields
  field_faithful := BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_field_faithful

theorem BaireCategoryCompleteMetricTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BaireCategoryCompleteMetricUp) ∧
      Nonempty (FieldFaithful BaireCategoryCompleteMetricUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact ⟨⟨baireCategoryCompleteMetricChapterTasteGate⟩, ⟨baireCategoryCompleteMetricFieldFaithful⟩⟩

end BEDC.Derived.BaireCategoryCompleteMetricUp
