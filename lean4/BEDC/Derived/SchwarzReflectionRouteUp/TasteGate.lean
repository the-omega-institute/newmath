import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchwarzReflectionRouteUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchwarzReflectionRouteUp : Type where
  | mk (U B J O H C P N : BHist) : SchwarzReflectionRouteUp
  deriving DecidableEq

def schwarzReflectionRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schwarzReflectionRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schwarzReflectionRouteEncodeBHist h

def schwarzReflectionRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schwarzReflectionRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schwarzReflectionRouteDecodeBHist tail)

private theorem SchwarzReflectionRouteTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def schwarzReflectionRouteFields : SchwarzReflectionRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SchwarzReflectionRouteUp.mk U B J O H C P N => [U, B, J, O, H, C, P, N]

def schwarzReflectionRouteToEventFlow : SchwarzReflectionRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SchwarzReflectionRouteUp.mk U B J O H C P N =>
      [[BMark.b0],
        schwarzReflectionRouteEncodeBHist U,
        [BMark.b1, BMark.b0],
        schwarzReflectionRouteEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        schwarzReflectionRouteEncodeBHist J,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        schwarzReflectionRouteEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        schwarzReflectionRouteEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        schwarzReflectionRouteEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        schwarzReflectionRouteEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        schwarzReflectionRouteEncodeBHist N]

private def schwarzReflectionRouteEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => schwarzReflectionRouteEventAtDefault index rest

def schwarzReflectionRouteFromEventFlow
    (ef : EventFlow) : Option SchwarzReflectionRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SchwarzReflectionRouteUp.mk
      (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEventAtDefault 1 ef))
      (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEventAtDefault 3 ef))
      (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEventAtDefault 5 ef))
      (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEventAtDefault 7 ef))
      (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEventAtDefault 9 ef))
      (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEventAtDefault 11 ef))
      (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEventAtDefault 13 ef))
      (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEventAtDefault 15 ef)))

private theorem SchwarzReflectionRouteTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SchwarzReflectionRouteUp,
      schwarzReflectionRouteFromEventFlow (schwarzReflectionRouteToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U B J O H C P N =>
      change
        some
          (SchwarzReflectionRouteUp.mk
            (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEncodeBHist U))
            (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEncodeBHist B))
            (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEncodeBHist J))
            (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEncodeBHist O))
            (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEncodeBHist H))
            (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEncodeBHist C))
            (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEncodeBHist P))
            (schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEncodeBHist N))) =
          some (SchwarzReflectionRouteUp.mk U B J O H C P N)
      rw [SchwarzReflectionRouteTasteGate_single_carrier_alignment_decode U,
        SchwarzReflectionRouteTasteGate_single_carrier_alignment_decode B,
        SchwarzReflectionRouteTasteGate_single_carrier_alignment_decode J,
        SchwarzReflectionRouteTasteGate_single_carrier_alignment_decode O,
        SchwarzReflectionRouteTasteGate_single_carrier_alignment_decode H,
        SchwarzReflectionRouteTasteGate_single_carrier_alignment_decode C,
        SchwarzReflectionRouteTasteGate_single_carrier_alignment_decode P,
        SchwarzReflectionRouteTasteGate_single_carrier_alignment_decode N]

private theorem SchwarzReflectionRouteTasteGate_single_carrier_alignment_injective
    {x y : SchwarzReflectionRouteUp} :
    schwarzReflectionRouteToEventFlow x = schwarzReflectionRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schwarzReflectionRouteFromEventFlow (schwarzReflectionRouteToEventFlow x) =
        schwarzReflectionRouteFromEventFlow (schwarzReflectionRouteToEventFlow y) :=
    congrArg schwarzReflectionRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SchwarzReflectionRouteTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SchwarzReflectionRouteTasteGate_single_carrier_alignment_round_trip y)))

private theorem SchwarzReflectionRouteTasteGate_single_carrier_alignment_fields :
    ∀ x y : SchwarzReflectionRouteUp,
      schwarzReflectionRouteFields x = schwarzReflectionRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ B₁ J₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk U₂ B₂ J₂ O₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance schwarzReflectionRouteBHistCarrier : BHistCarrier SchwarzReflectionRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schwarzReflectionRouteToEventFlow
  fromEventFlow := schwarzReflectionRouteFromEventFlow

instance schwarzReflectionRouteChapterTasteGate :
    ChapterTasteGate SchwarzReflectionRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schwarzReflectionRouteFromEventFlow (schwarzReflectionRouteToEventFlow x) = some x
    exact SchwarzReflectionRouteTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SchwarzReflectionRouteTasteGate_single_carrier_alignment_injective heq)

instance schwarzReflectionRouteFieldFaithful :
    FieldFaithful SchwarzReflectionRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := schwarzReflectionRouteFields
  field_faithful := SchwarzReflectionRouteTasteGate_single_carrier_alignment_fields

instance schwarzReflectionRouteNontrivial : Nontrivial SchwarzReflectionRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SchwarzReflectionRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SchwarzReflectionRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SchwarzReflectionRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  schwarzReflectionRouteChapterTasteGate

theorem SchwarzReflectionRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      schwarzReflectionRouteDecodeBHist (schwarzReflectionRouteEncodeBHist h) = h) ∧
      schwarzReflectionRouteEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x y : SchwarzReflectionRouteUp,
          schwarzReflectionRouteFields x = schwarzReflectionRouteFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SchwarzReflectionRouteTasteGate_single_carrier_alignment_decode,
      rfl,
      SchwarzReflectionRouteTasteGate_single_carrier_alignment_fields⟩

end BEDC.Derived.SchwarzReflectionRouteUp.TasteGate
