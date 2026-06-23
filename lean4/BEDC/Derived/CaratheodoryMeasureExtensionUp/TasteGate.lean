import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CaratheodoryMeasureExtensionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CaratheodoryMeasureExtensionUp : Type where
  | mk
      (premeasure schedule outerMeasure targetMeasure exactness transport continuation
        provenance nameCert : BHist) :
      CaratheodoryMeasureExtensionUp
  deriving DecidableEq

def caratheodoryMeasureExtensionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: caratheodoryMeasureExtensionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: caratheodoryMeasureExtensionEncodeBHist h

def caratheodoryMeasureExtensionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (caratheodoryMeasureExtensionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (caratheodoryMeasureExtensionDecodeBHist tail)

private theorem CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      caratheodoryMeasureExtensionDecodeBHist
          (caratheodoryMeasureExtensionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def caratheodoryMeasureExtensionFields : CaratheodoryMeasureExtensionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CaratheodoryMeasureExtensionUp.mk premeasure schedule outerMeasure targetMeasure
      exactness transport continuation provenance nameCert =>
      [premeasure, schedule, outerMeasure, targetMeasure, exactness, transport,
        continuation, provenance, nameCert]

def caratheodoryMeasureExtensionToEventFlow : CaratheodoryMeasureExtensionUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (caratheodoryMeasureExtensionFields x).map caratheodoryMeasureExtensionEncodeBHist

private def caratheodoryMeasureExtensionEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => caratheodoryMeasureExtensionEventAt index rest

def caratheodoryMeasureExtensionFromEventFlow
    (ef : EventFlow) : Option CaratheodoryMeasureExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CaratheodoryMeasureExtensionUp.mk
      (caratheodoryMeasureExtensionDecodeBHist
        (caratheodoryMeasureExtensionEventAt 0 ef))
      (caratheodoryMeasureExtensionDecodeBHist
        (caratheodoryMeasureExtensionEventAt 1 ef))
      (caratheodoryMeasureExtensionDecodeBHist
        (caratheodoryMeasureExtensionEventAt 2 ef))
      (caratheodoryMeasureExtensionDecodeBHist
        (caratheodoryMeasureExtensionEventAt 3 ef))
      (caratheodoryMeasureExtensionDecodeBHist
        (caratheodoryMeasureExtensionEventAt 4 ef))
      (caratheodoryMeasureExtensionDecodeBHist
        (caratheodoryMeasureExtensionEventAt 5 ef))
      (caratheodoryMeasureExtensionDecodeBHist
        (caratheodoryMeasureExtensionEventAt 6 ef))
      (caratheodoryMeasureExtensionDecodeBHist
        (caratheodoryMeasureExtensionEventAt 7 ef))
      (caratheodoryMeasureExtensionDecodeBHist
        (caratheodoryMeasureExtensionEventAt 8 ef)))

private theorem CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_round_trip
    (x : CaratheodoryMeasureExtensionUp) :
    caratheodoryMeasureExtensionFromEventFlow
        (caratheodoryMeasureExtensionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk premeasure schedule outerMeasure targetMeasure exactness transport continuation
      provenance nameCert =>
      change
        some
          (CaratheodoryMeasureExtensionUp.mk
            (caratheodoryMeasureExtensionDecodeBHist
              (caratheodoryMeasureExtensionEncodeBHist premeasure))
            (caratheodoryMeasureExtensionDecodeBHist
              (caratheodoryMeasureExtensionEncodeBHist schedule))
            (caratheodoryMeasureExtensionDecodeBHist
              (caratheodoryMeasureExtensionEncodeBHist outerMeasure))
            (caratheodoryMeasureExtensionDecodeBHist
              (caratheodoryMeasureExtensionEncodeBHist targetMeasure))
            (caratheodoryMeasureExtensionDecodeBHist
              (caratheodoryMeasureExtensionEncodeBHist exactness))
            (caratheodoryMeasureExtensionDecodeBHist
              (caratheodoryMeasureExtensionEncodeBHist transport))
            (caratheodoryMeasureExtensionDecodeBHist
              (caratheodoryMeasureExtensionEncodeBHist continuation))
            (caratheodoryMeasureExtensionDecodeBHist
              (caratheodoryMeasureExtensionEncodeBHist provenance))
            (caratheodoryMeasureExtensionDecodeBHist
              (caratheodoryMeasureExtensionEncodeBHist nameCert))) =
          some
            (CaratheodoryMeasureExtensionUp.mk premeasure schedule outerMeasure targetMeasure
              exactness transport continuation provenance nameCert)
      rw [CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_decode_encode
          premeasure,
        CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_decode_encode schedule,
        CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_decode_encode
          outerMeasure,
        CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_decode_encode
          targetMeasure,
        CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_decode_encode exactness,
        CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_decode_encode transport,
        CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_decode_encode
          continuation,
        CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_decode_encode
          provenance,
        CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CaratheodoryMeasureExtensionUp} :
    caratheodoryMeasureExtensionToEventFlow x =
        caratheodoryMeasureExtensionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      caratheodoryMeasureExtensionFromEventFlow
          (caratheodoryMeasureExtensionToEventFlow x) =
        caratheodoryMeasureExtensionFromEventFlow
          (caratheodoryMeasureExtensionToEventFlow y) :=
    congrArg caratheodoryMeasureExtensionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_round_trip y)))

instance caratheodoryMeasureExtensionBHistCarrier :
    BHistCarrier CaratheodoryMeasureExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := caratheodoryMeasureExtensionToEventFlow
  fromEventFlow := caratheodoryMeasureExtensionFromEventFlow

instance caratheodoryMeasureExtensionChapterTasteGate :
    ChapterTasteGate CaratheodoryMeasureExtensionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      caratheodoryMeasureExtensionFromEventFlow
          (caratheodoryMeasureExtensionToEventFlow x) =
        some x
    exact CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate CaratheodoryMeasureExtensionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  caratheodoryMeasureExtensionChapterTasteGate

theorem CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      caratheodoryMeasureExtensionDecodeBHist
          (caratheodoryMeasureExtensionEncodeBHist h) =
        h) ∧
      (∀ x : CaratheodoryMeasureExtensionUp,
        caratheodoryMeasureExtensionFromEventFlow
            (caratheodoryMeasureExtensionToEventFlow x) =
          some x) ∧
        caratheodoryMeasureExtensionEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_decode_encode,
      CaratheodoryMeasureExtensionTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.CaratheodoryMeasureExtensionUp
