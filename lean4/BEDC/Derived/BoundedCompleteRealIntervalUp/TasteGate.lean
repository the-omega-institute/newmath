import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedCompleteRealIntervalUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedCompleteRealIntervalUp : Type where
  | mk (B D W R E H C P N : BHist) : BoundedCompleteRealIntervalUp
  deriving DecidableEq

def boundedCompleteRealIntervalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedCompleteRealIntervalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedCompleteRealIntervalEncodeBHist h

def boundedCompleteRealIntervalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedCompleteRealIntervalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedCompleteRealIntervalDecodeBHist tail)

private theorem BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      boundedCompleteRealIntervalDecodeBHist
        (boundedCompleteRealIntervalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedCompleteRealIntervalFields : BoundedCompleteRealIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedCompleteRealIntervalUp.mk B D W R E H C P N => [B, D, W, R, E, H, C, P, N]

def boundedCompleteRealIntervalToEventFlow : BoundedCompleteRealIntervalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map boundedCompleteRealIntervalEncodeBHist (boundedCompleteRealIntervalFields x)

private def boundedCompleteRealIntervalEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedCompleteRealIntervalEventAtDefault index rest

def boundedCompleteRealIntervalFromEventFlow
    (ef : EventFlow) : Option BoundedCompleteRealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedCompleteRealIntervalUp.mk
      (boundedCompleteRealIntervalDecodeBHist (boundedCompleteRealIntervalEventAtDefault 0 ef))
      (boundedCompleteRealIntervalDecodeBHist (boundedCompleteRealIntervalEventAtDefault 1 ef))
      (boundedCompleteRealIntervalDecodeBHist (boundedCompleteRealIntervalEventAtDefault 2 ef))
      (boundedCompleteRealIntervalDecodeBHist (boundedCompleteRealIntervalEventAtDefault 3 ef))
      (boundedCompleteRealIntervalDecodeBHist (boundedCompleteRealIntervalEventAtDefault 4 ef))
      (boundedCompleteRealIntervalDecodeBHist (boundedCompleteRealIntervalEventAtDefault 5 ef))
      (boundedCompleteRealIntervalDecodeBHist (boundedCompleteRealIntervalEventAtDefault 6 ef))
      (boundedCompleteRealIntervalDecodeBHist (boundedCompleteRealIntervalEventAtDefault 7 ef))
      (boundedCompleteRealIntervalDecodeBHist (boundedCompleteRealIntervalEventAtDefault 8 ef)))

private theorem BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedCompleteRealIntervalUp,
      boundedCompleteRealIntervalFromEventFlow
        (boundedCompleteRealIntervalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B D W R E H C P N =>
      change
        some
          (BoundedCompleteRealIntervalUp.mk
            (boundedCompleteRealIntervalDecodeBHist
              (boundedCompleteRealIntervalEncodeBHist B))
            (boundedCompleteRealIntervalDecodeBHist
              (boundedCompleteRealIntervalEncodeBHist D))
            (boundedCompleteRealIntervalDecodeBHist
              (boundedCompleteRealIntervalEncodeBHist W))
            (boundedCompleteRealIntervalDecodeBHist
              (boundedCompleteRealIntervalEncodeBHist R))
            (boundedCompleteRealIntervalDecodeBHist
              (boundedCompleteRealIntervalEncodeBHist E))
            (boundedCompleteRealIntervalDecodeBHist
              (boundedCompleteRealIntervalEncodeBHist H))
            (boundedCompleteRealIntervalDecodeBHist
              (boundedCompleteRealIntervalEncodeBHist C))
            (boundedCompleteRealIntervalDecodeBHist
              (boundedCompleteRealIntervalEncodeBHist P))
            (boundedCompleteRealIntervalDecodeBHist
              (boundedCompleteRealIntervalEncodeBHist N))) =
          some (BoundedCompleteRealIntervalUp.mk B D W R E H C P N)
      rw [BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_decode B,
        BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_decode D,
        BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_decode W,
        BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_decode R,
        BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_decode E,
        BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_decode H,
        BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_decode C,
        BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_decode P,
        BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_decode N]

private theorem BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_injective
    {x y : BoundedCompleteRealIntervalUp} :
    boundedCompleteRealIntervalToEventFlow x = boundedCompleteRealIntervalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedCompleteRealIntervalFromEventFlow (boundedCompleteRealIntervalToEventFlow x) =
        boundedCompleteRealIntervalFromEventFlow (boundedCompleteRealIntervalToEventFlow y) :=
    congrArg boundedCompleteRealIntervalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_round_trip y)))

private theorem BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_fields :
    ∀ x y : BoundedCompleteRealIntervalUp,
      boundedCompleteRealIntervalFields x = boundedCompleteRealIntervalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 D1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 D2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance boundedCompleteRealIntervalBHistCarrier :
    BHistCarrier BoundedCompleteRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedCompleteRealIntervalToEventFlow
  fromEventFlow := boundedCompleteRealIntervalFromEventFlow

instance boundedCompleteRealIntervalChapterTasteGate :
    ChapterTasteGate BoundedCompleteRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedCompleteRealIntervalFromEventFlow (boundedCompleteRealIntervalToEventFlow x) =
        some x
    exact BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_injective heq)

instance boundedCompleteRealIntervalFieldFaithful :
    FieldFaithful BoundedCompleteRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := boundedCompleteRealIntervalFields
  field_faithful := BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_fields

instance boundedCompleteRealIntervalInhabited : Inhabited BoundedCompleteRealIntervalUp where
  -- BEDC touchpoint anchor: BHist BMark
  default :=
    BoundedCompleteRealIntervalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty

def taste_gate : ChapterTasteGate BoundedCompleteRealIntervalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedCompleteRealIntervalChapterTasteGate

theorem BoundedCompleteRealIntervalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      boundedCompleteRealIntervalDecodeBHist
        (boundedCompleteRealIntervalEncodeBHist h) = h) ∧
      FieldFaithful.field_count BoundedCompleteRealIntervalUp = 9 ∧
        boundedCompleteRealIntervalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨BoundedCompleteRealIntervalTasteGate_single_carrier_alignment_decode,
      rfl,
      rfl⟩

end BEDC.Derived.BoundedCompleteRealIntervalUp.TasteGate
