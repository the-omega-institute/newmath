import BEDC.Derived.GaugeIntegralUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GaugeIntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate
open BEDC.Derived

def gaugeIntegralEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gaugeIntegralEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gaugeIntegralEncodeBHist h

def gaugeIntegralDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gaugeIntegralDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gaugeIntegralDecodeBHist tail)

private theorem GaugeIntegralTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, gaugeIntegralDecodeBHist (gaugeIntegralEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def gaugeIntegralToEventFlow : GaugeIntegralUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GaugeIntegralUp.mk I Gamma T S D Q R H C P N =>
      [[BMark.b0],
        gaugeIntegralEncodeBHist I,
        [BMark.b1, BMark.b0],
        gaugeIntegralEncodeBHist Gamma,
        [BMark.b1, BMark.b1, BMark.b0],
        gaugeIntegralEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gaugeIntegralEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gaugeIntegralEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gaugeIntegralEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gaugeIntegralEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        gaugeIntegralEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        gaugeIntegralEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        gaugeIntegralEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        gaugeIntegralEncodeBHist N]

private def gaugeIntegralEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => gaugeIntegralEventAtDefault index rest

def gaugeIntegralFromEventFlow (ef : EventFlow) : Option GaugeIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GaugeIntegralUp.mk
      (gaugeIntegralDecodeBHist (gaugeIntegralEventAtDefault 1 ef))
      (gaugeIntegralDecodeBHist (gaugeIntegralEventAtDefault 3 ef))
      (gaugeIntegralDecodeBHist (gaugeIntegralEventAtDefault 5 ef))
      (gaugeIntegralDecodeBHist (gaugeIntegralEventAtDefault 7 ef))
      (gaugeIntegralDecodeBHist (gaugeIntegralEventAtDefault 9 ef))
      (gaugeIntegralDecodeBHist (gaugeIntegralEventAtDefault 11 ef))
      (gaugeIntegralDecodeBHist (gaugeIntegralEventAtDefault 13 ef))
      (gaugeIntegralDecodeBHist (gaugeIntegralEventAtDefault 15 ef))
      (gaugeIntegralDecodeBHist (gaugeIntegralEventAtDefault 17 ef))
      (gaugeIntegralDecodeBHist (gaugeIntegralEventAtDefault 19 ef))
      (gaugeIntegralDecodeBHist (gaugeIntegralEventAtDefault 21 ef)))

private theorem GaugeIntegralTasteGate_single_carrier_alignment_round_trip :
    forall x : GaugeIntegralUp,
      gaugeIntegralFromEventFlow (gaugeIntegralToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I Gamma T S D Q R H C P N =>
      change
        some
          (GaugeIntegralUp.mk
            (gaugeIntegralDecodeBHist (gaugeIntegralEncodeBHist I))
            (gaugeIntegralDecodeBHist (gaugeIntegralEncodeBHist Gamma))
            (gaugeIntegralDecodeBHist (gaugeIntegralEncodeBHist T))
            (gaugeIntegralDecodeBHist (gaugeIntegralEncodeBHist S))
            (gaugeIntegralDecodeBHist (gaugeIntegralEncodeBHist D))
            (gaugeIntegralDecodeBHist (gaugeIntegralEncodeBHist Q))
            (gaugeIntegralDecodeBHist (gaugeIntegralEncodeBHist R))
            (gaugeIntegralDecodeBHist (gaugeIntegralEncodeBHist H))
            (gaugeIntegralDecodeBHist (gaugeIntegralEncodeBHist C))
            (gaugeIntegralDecodeBHist (gaugeIntegralEncodeBHist P))
            (gaugeIntegralDecodeBHist (gaugeIntegralEncodeBHist N))) =
          some (GaugeIntegralUp.mk I Gamma T S D Q R H C P N)
      rw [GaugeIntegralTasteGate_single_carrier_alignment_decode_encode I,
        GaugeIntegralTasteGate_single_carrier_alignment_decode_encode Gamma,
        GaugeIntegralTasteGate_single_carrier_alignment_decode_encode T,
        GaugeIntegralTasteGate_single_carrier_alignment_decode_encode S,
        GaugeIntegralTasteGate_single_carrier_alignment_decode_encode D,
        GaugeIntegralTasteGate_single_carrier_alignment_decode_encode Q,
        GaugeIntegralTasteGate_single_carrier_alignment_decode_encode R,
        GaugeIntegralTasteGate_single_carrier_alignment_decode_encode H,
        GaugeIntegralTasteGate_single_carrier_alignment_decode_encode C,
        GaugeIntegralTasteGate_single_carrier_alignment_decode_encode P,
        GaugeIntegralTasteGate_single_carrier_alignment_decode_encode N]

private theorem GaugeIntegralTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GaugeIntegralUp} :
    gaugeIntegralToEventFlow x = gaugeIntegralToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gaugeIntegralFromEventFlow (gaugeIntegralToEventFlow x) =
        gaugeIntegralFromEventFlow (gaugeIntegralToEventFlow y) :=
    congrArg gaugeIntegralFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (GaugeIntegralTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GaugeIntegralTasteGate_single_carrier_alignment_round_trip y)))

private def gaugeIntegralFields : GaugeIntegralUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GaugeIntegralUp.mk I Gamma T S D Q R H C P N => [I, Gamma, T, S, D, Q, R, H, C, P, N]

private theorem GaugeIntegralTasteGate_single_carrier_alignment_fields :
    forall x y : GaugeIntegralUp, gaugeIntegralFields x = gaugeIntegralFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 Gamma1 T1 S1 D1 Q1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 Gamma2 T2 S2 D2 Q2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance gaugeIntegralBHistCarrier : BHistCarrier GaugeIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gaugeIntegralToEventFlow
  fromEventFlow := gaugeIntegralFromEventFlow

instance gaugeIntegralChapterTasteGate : ChapterTasteGate GaugeIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gaugeIntegralFromEventFlow (gaugeIntegralToEventFlow x) = some x
    exact GaugeIntegralTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GaugeIntegralTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance gaugeIntegralFieldFaithful : FieldFaithful GaugeIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := gaugeIntegralFields
  field_faithful := GaugeIntegralTasteGate_single_carrier_alignment_fields

instance gaugeIntegralNontrivial : Nontrivial GaugeIntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GaugeIntegralUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GaugeIntegralUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate GaugeIntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  gaugeIntegralChapterTasteGate

theorem GaugeIntegralTasteGate_single_carrier_alignment :
    (forall h : BHist, gaugeIntegralDecodeBHist (gaugeIntegralEncodeBHist h) = h) ∧
      (forall x : GaugeIntegralUp,
        gaugeIntegralFromEventFlow (gaugeIntegralToEventFlow x) = some x) ∧
        (forall x y : GaugeIntegralUp,
          gaugeIntegralToEventFlow x = gaugeIntegralToEventFlow y -> x = y) ∧
          gaugeIntegralEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨GaugeIntegralTasteGate_single_carrier_alignment_decode_encode,
      GaugeIntegralTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => GaugeIntegralTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.GaugeIntegralUp
