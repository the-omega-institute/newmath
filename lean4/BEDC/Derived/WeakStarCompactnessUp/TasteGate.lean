import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WeakStarCompactnessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WeakStarCompactnessUp : Type where
  | mk (E T B A C R H Q P N : BHist) : WeakStarCompactnessUp
  deriving DecidableEq

def weakStarCompactnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: weakStarCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: weakStarCompactnessEncodeBHist h

def weakStarCompactnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (weakStarCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (weakStarCompactnessDecodeBHist tail)

private theorem WeakStarCompactnessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      weakStarCompactnessDecodeBHist (weakStarCompactnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def weakStarCompactnessFields : WeakStarCompactnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | WeakStarCompactnessUp.mk E T B A C R H Q P N => [E, T, B, A, C, R, H, Q, P, N]

def weakStarCompactnessToEventFlow : WeakStarCompactnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map weakStarCompactnessEncodeBHist (weakStarCompactnessFields x)

private def weakStarCompactnessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => weakStarCompactnessEventAtDefault index rest

def weakStarCompactnessFromEventFlow (ef : EventFlow) : Option WeakStarCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (WeakStarCompactnessUp.mk
      (weakStarCompactnessDecodeBHist (weakStarCompactnessEventAtDefault 0 ef))
      (weakStarCompactnessDecodeBHist (weakStarCompactnessEventAtDefault 1 ef))
      (weakStarCompactnessDecodeBHist (weakStarCompactnessEventAtDefault 2 ef))
      (weakStarCompactnessDecodeBHist (weakStarCompactnessEventAtDefault 3 ef))
      (weakStarCompactnessDecodeBHist (weakStarCompactnessEventAtDefault 4 ef))
      (weakStarCompactnessDecodeBHist (weakStarCompactnessEventAtDefault 5 ef))
      (weakStarCompactnessDecodeBHist (weakStarCompactnessEventAtDefault 6 ef))
      (weakStarCompactnessDecodeBHist (weakStarCompactnessEventAtDefault 7 ef))
      (weakStarCompactnessDecodeBHist (weakStarCompactnessEventAtDefault 8 ef))
      (weakStarCompactnessDecodeBHist (weakStarCompactnessEventAtDefault 9 ef)))

private theorem WeakStarCompactnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : WeakStarCompactnessUp,
      weakStarCompactnessFromEventFlow (weakStarCompactnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E T B A C R H Q P N =>
      change
        some
          (WeakStarCompactnessUp.mk
            (weakStarCompactnessDecodeBHist (weakStarCompactnessEncodeBHist E))
            (weakStarCompactnessDecodeBHist (weakStarCompactnessEncodeBHist T))
            (weakStarCompactnessDecodeBHist (weakStarCompactnessEncodeBHist B))
            (weakStarCompactnessDecodeBHist (weakStarCompactnessEncodeBHist A))
            (weakStarCompactnessDecodeBHist (weakStarCompactnessEncodeBHist C))
            (weakStarCompactnessDecodeBHist (weakStarCompactnessEncodeBHist R))
            (weakStarCompactnessDecodeBHist (weakStarCompactnessEncodeBHist H))
            (weakStarCompactnessDecodeBHist (weakStarCompactnessEncodeBHist Q))
            (weakStarCompactnessDecodeBHist (weakStarCompactnessEncodeBHist P))
            (weakStarCompactnessDecodeBHist (weakStarCompactnessEncodeBHist N))) =
          some (WeakStarCompactnessUp.mk E T B A C R H Q P N)
      rw [WeakStarCompactnessTasteGate_single_carrier_alignment_decode E,
        WeakStarCompactnessTasteGate_single_carrier_alignment_decode T,
        WeakStarCompactnessTasteGate_single_carrier_alignment_decode B,
        WeakStarCompactnessTasteGate_single_carrier_alignment_decode A,
        WeakStarCompactnessTasteGate_single_carrier_alignment_decode C,
        WeakStarCompactnessTasteGate_single_carrier_alignment_decode R,
        WeakStarCompactnessTasteGate_single_carrier_alignment_decode H,
        WeakStarCompactnessTasteGate_single_carrier_alignment_decode Q,
        WeakStarCompactnessTasteGate_single_carrier_alignment_decode P,
        WeakStarCompactnessTasteGate_single_carrier_alignment_decode N]

private theorem WeakStarCompactnessTasteGate_single_carrier_alignment_injective
    {x y : WeakStarCompactnessUp} :
    weakStarCompactnessToEventFlow x = weakStarCompactnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      weakStarCompactnessFromEventFlow (weakStarCompactnessToEventFlow x) =
        weakStarCompactnessFromEventFlow (weakStarCompactnessToEventFlow y) :=
    congrArg weakStarCompactnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (WeakStarCompactnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (WeakStarCompactnessTasteGate_single_carrier_alignment_round_trip y)))

private theorem WeakStarCompactnessTasteGate_single_carrier_alignment_fields :
    ∀ x y : WeakStarCompactnessUp, weakStarCompactnessFields x = weakStarCompactnessFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E1 T1 B1 A1 C1 R1 H1 Q1 P1 N1 =>
      cases y with
      | mk E2 T2 B2 A2 C2 R2 H2 Q2 P2 N2 =>
          cases hfields
          rfl

instance weakStarCompactnessBHistCarrier : BHistCarrier WeakStarCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := weakStarCompactnessToEventFlow
  fromEventFlow := weakStarCompactnessFromEventFlow

instance weakStarCompactnessChapterTasteGate : ChapterTasteGate WeakStarCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change weakStarCompactnessFromEventFlow (weakStarCompactnessToEventFlow x) = some x
    exact WeakStarCompactnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (WeakStarCompactnessTasteGate_single_carrier_alignment_injective heq)

instance weakStarCompactnessFieldFaithful : FieldFaithful WeakStarCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := weakStarCompactnessFields
  field_faithful := WeakStarCompactnessTasteGate_single_carrier_alignment_fields

instance weakStarCompactnessInhabited : Inhabited WeakStarCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  default :=
    WeakStarCompactnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty

def taste_gate : ChapterTasteGate WeakStarCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  weakStarCompactnessChapterTasteGate

theorem WeakStarCompactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, weakStarCompactnessDecodeBHist (weakStarCompactnessEncodeBHist h) = h) ∧
      FieldFaithful.field_count WeakStarCompactnessUp = 10 ∧
        weakStarCompactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨WeakStarCompactnessTasteGate_single_carrier_alignment_decode,
      rfl,
      rfl⟩

end BEDC.Derived.WeakStarCompactnessUp.TasteGate
