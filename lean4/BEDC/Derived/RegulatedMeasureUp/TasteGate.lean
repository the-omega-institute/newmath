import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatedMeasureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedMeasureUp : Type where
  | mk (F V Pi Delta R E H C P N : BHist) : RegulatedMeasureUp
  deriving DecidableEq

def regulatedMeasureEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regulatedMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regulatedMeasureEncodeBHist h

def regulatedMeasureDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regulatedMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regulatedMeasureDecodeBHist tail)

private theorem RegulatedMeasureTasteGate_single_carrier_alignment_decode :
    forall h : BHist, regulatedMeasureDecodeBHist (regulatedMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regulatedMeasureToEventFlow : RegulatedMeasureUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedMeasureUp.mk F V Pi Delta R E H C P N =>
      [[BMark.b0],
        regulatedMeasureEncodeBHist F,
        [BMark.b1, BMark.b0],
        regulatedMeasureEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b0],
        regulatedMeasureEncodeBHist Pi,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regulatedMeasureEncodeBHist Delta,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regulatedMeasureEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regulatedMeasureEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regulatedMeasureEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regulatedMeasureEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regulatedMeasureEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regulatedMeasureEncodeBHist N]

private def regulatedMeasureEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regulatedMeasureEventAtDefault index rest

def regulatedMeasureFromEventFlow (ef : EventFlow) : Option RegulatedMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegulatedMeasureUp.mk
      (regulatedMeasureDecodeBHist (regulatedMeasureEventAtDefault 1 ef))
      (regulatedMeasureDecodeBHist (regulatedMeasureEventAtDefault 3 ef))
      (regulatedMeasureDecodeBHist (regulatedMeasureEventAtDefault 5 ef))
      (regulatedMeasureDecodeBHist (regulatedMeasureEventAtDefault 7 ef))
      (regulatedMeasureDecodeBHist (regulatedMeasureEventAtDefault 9 ef))
      (regulatedMeasureDecodeBHist (regulatedMeasureEventAtDefault 11 ef))
      (regulatedMeasureDecodeBHist (regulatedMeasureEventAtDefault 13 ef))
      (regulatedMeasureDecodeBHist (regulatedMeasureEventAtDefault 15 ef))
      (regulatedMeasureDecodeBHist (regulatedMeasureEventAtDefault 17 ef))
      (regulatedMeasureDecodeBHist (regulatedMeasureEventAtDefault 19 ef)))

private theorem RegulatedMeasureTasteGate_single_carrier_alignment_round_trip :
    forall x : RegulatedMeasureUp,
      regulatedMeasureFromEventFlow (regulatedMeasureToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F V Pi Delta R E H C P N =>
      change
        some
          (RegulatedMeasureUp.mk
            (regulatedMeasureDecodeBHist (regulatedMeasureEncodeBHist F))
            (regulatedMeasureDecodeBHist (regulatedMeasureEncodeBHist V))
            (regulatedMeasureDecodeBHist (regulatedMeasureEncodeBHist Pi))
            (regulatedMeasureDecodeBHist (regulatedMeasureEncodeBHist Delta))
            (regulatedMeasureDecodeBHist (regulatedMeasureEncodeBHist R))
            (regulatedMeasureDecodeBHist (regulatedMeasureEncodeBHist E))
            (regulatedMeasureDecodeBHist (regulatedMeasureEncodeBHist H))
            (regulatedMeasureDecodeBHist (regulatedMeasureEncodeBHist C))
            (regulatedMeasureDecodeBHist (regulatedMeasureEncodeBHist P))
            (regulatedMeasureDecodeBHist (regulatedMeasureEncodeBHist N))) =
          some (RegulatedMeasureUp.mk F V Pi Delta R E H C P N)
      rw [RegulatedMeasureTasteGate_single_carrier_alignment_decode F,
        RegulatedMeasureTasteGate_single_carrier_alignment_decode V,
        RegulatedMeasureTasteGate_single_carrier_alignment_decode Pi,
        RegulatedMeasureTasteGate_single_carrier_alignment_decode Delta,
        RegulatedMeasureTasteGate_single_carrier_alignment_decode R,
        RegulatedMeasureTasteGate_single_carrier_alignment_decode E,
        RegulatedMeasureTasteGate_single_carrier_alignment_decode H,
        RegulatedMeasureTasteGate_single_carrier_alignment_decode C,
        RegulatedMeasureTasteGate_single_carrier_alignment_decode P,
        RegulatedMeasureTasteGate_single_carrier_alignment_decode N]

private theorem RegulatedMeasureTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegulatedMeasureUp} :
    regulatedMeasureToEventFlow x = regulatedMeasureToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regulatedMeasureFromEventFlow (regulatedMeasureToEventFlow x) =
        regulatedMeasureFromEventFlow (regulatedMeasureToEventFlow y) :=
    congrArg regulatedMeasureFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegulatedMeasureTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegulatedMeasureTasteGate_single_carrier_alignment_round_trip y)))

private def regulatedMeasureFields : RegulatedMeasureUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedMeasureUp.mk F V Pi Delta R E H C P N => [F, V, Pi, Delta, R, E, H, C, P, N]

private theorem RegulatedMeasureTasteGate_single_carrier_alignment_fields :
    forall x y : RegulatedMeasureUp, regulatedMeasureFields x = regulatedMeasureFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 V1 Pi1 Delta1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 V2 Pi2 Delta2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regulatedMeasureBHistCarrier : BHistCarrier RegulatedMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regulatedMeasureToEventFlow
  fromEventFlow := regulatedMeasureFromEventFlow

instance regulatedMeasureChapterTasteGate : ChapterTasteGate RegulatedMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regulatedMeasureFromEventFlow (regulatedMeasureToEventFlow x) = some x
    exact RegulatedMeasureTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegulatedMeasureTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regulatedMeasureFieldFaithful : FieldFaithful RegulatedMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regulatedMeasureFields
  field_faithful := RegulatedMeasureTasteGate_single_carrier_alignment_fields

instance regulatedMeasureNontrivial : Nontrivial RegulatedMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegulatedMeasureUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegulatedMeasureUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegulatedMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regulatedMeasureChapterTasteGate

namespace TasteGate

theorem RegulatedMeasureTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegulatedMeasureUp) ∧
      Nonempty (FieldFaithful RegulatedMeasureUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegulatedMeasureUp) ∧
          (∀ h : BHist, regulatedMeasureDecodeBHist (regulatedMeasureEncodeBHist h) = h) ∧
            regulatedMeasureEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨regulatedMeasureChapterTasteGate⟩,
      ⟨regulatedMeasureFieldFaithful⟩,
      ⟨regulatedMeasureNontrivial⟩,
      RegulatedMeasureTasteGate_single_carrier_alignment_decode,
      rfl⟩

end TasteGate

end BEDC.Derived.RegulatedMeasureUp
