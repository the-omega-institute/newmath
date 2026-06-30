import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FirmNonexpansiveProjectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FirmNonexpansiveProjectionCarrier : Type where
  | mk (H K M E S D L T C P N : BHist) : FirmNonexpansiveProjectionCarrier
  deriving DecidableEq

def firmNonexpansiveProjectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: firmNonexpansiveProjectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: firmNonexpansiveProjectionEncodeBHist h

def firmNonexpansiveProjectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (firmNonexpansiveProjectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (firmNonexpansiveProjectionDecodeBHist tail)

private theorem firmNonexpansiveProjection_decode_encode_bhist :
    ∀ h : BHist,
      firmNonexpansiveProjectionDecodeBHist
        (firmNonexpansiveProjectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def firmNonexpansiveProjectionToEventFlow :
    FirmNonexpansiveProjectionCarrier → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FirmNonexpansiveProjectionCarrier.mk H K M E S D L T C P N =>
      [firmNonexpansiveProjectionEncodeBHist H,
        firmNonexpansiveProjectionEncodeBHist K,
        firmNonexpansiveProjectionEncodeBHist M,
        firmNonexpansiveProjectionEncodeBHist E,
        firmNonexpansiveProjectionEncodeBHist S,
        firmNonexpansiveProjectionEncodeBHist D,
        firmNonexpansiveProjectionEncodeBHist L,
        firmNonexpansiveProjectionEncodeBHist T,
        firmNonexpansiveProjectionEncodeBHist C,
        firmNonexpansiveProjectionEncodeBHist P,
        firmNonexpansiveProjectionEncodeBHist N]

private def firmNonexpansiveProjectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => firmNonexpansiveProjectionEventAtDefault index rest

def firmNonexpansiveProjectionFromEventFlow (ef : EventFlow) :
    Option FirmNonexpansiveProjectionCarrier :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FirmNonexpansiveProjectionCarrier.mk
      (firmNonexpansiveProjectionDecodeBHist
        (firmNonexpansiveProjectionEventAtDefault 0 ef))
      (firmNonexpansiveProjectionDecodeBHist
        (firmNonexpansiveProjectionEventAtDefault 1 ef))
      (firmNonexpansiveProjectionDecodeBHist
        (firmNonexpansiveProjectionEventAtDefault 2 ef))
      (firmNonexpansiveProjectionDecodeBHist
        (firmNonexpansiveProjectionEventAtDefault 3 ef))
      (firmNonexpansiveProjectionDecodeBHist
        (firmNonexpansiveProjectionEventAtDefault 4 ef))
      (firmNonexpansiveProjectionDecodeBHist
        (firmNonexpansiveProjectionEventAtDefault 5 ef))
      (firmNonexpansiveProjectionDecodeBHist
        (firmNonexpansiveProjectionEventAtDefault 6 ef))
      (firmNonexpansiveProjectionDecodeBHist
        (firmNonexpansiveProjectionEventAtDefault 7 ef))
      (firmNonexpansiveProjectionDecodeBHist
        (firmNonexpansiveProjectionEventAtDefault 8 ef))
      (firmNonexpansiveProjectionDecodeBHist
        (firmNonexpansiveProjectionEventAtDefault 9 ef))
      (firmNonexpansiveProjectionDecodeBHist
        (firmNonexpansiveProjectionEventAtDefault 10 ef)))

private theorem firmNonexpansiveProjection_round_trip
    (x : FirmNonexpansiveProjectionCarrier) :
    firmNonexpansiveProjectionFromEventFlow
      (firmNonexpansiveProjectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk H K M E S D L T C P N =>
      change
        some
          (FirmNonexpansiveProjectionCarrier.mk
            (firmNonexpansiveProjectionDecodeBHist
              (firmNonexpansiveProjectionEncodeBHist H))
            (firmNonexpansiveProjectionDecodeBHist
              (firmNonexpansiveProjectionEncodeBHist K))
            (firmNonexpansiveProjectionDecodeBHist
              (firmNonexpansiveProjectionEncodeBHist M))
            (firmNonexpansiveProjectionDecodeBHist
              (firmNonexpansiveProjectionEncodeBHist E))
            (firmNonexpansiveProjectionDecodeBHist
              (firmNonexpansiveProjectionEncodeBHist S))
            (firmNonexpansiveProjectionDecodeBHist
              (firmNonexpansiveProjectionEncodeBHist D))
            (firmNonexpansiveProjectionDecodeBHist
              (firmNonexpansiveProjectionEncodeBHist L))
            (firmNonexpansiveProjectionDecodeBHist
              (firmNonexpansiveProjectionEncodeBHist T))
            (firmNonexpansiveProjectionDecodeBHist
              (firmNonexpansiveProjectionEncodeBHist C))
            (firmNonexpansiveProjectionDecodeBHist
              (firmNonexpansiveProjectionEncodeBHist P))
            (firmNonexpansiveProjectionDecodeBHist
              (firmNonexpansiveProjectionEncodeBHist N))) =
          some (FirmNonexpansiveProjectionCarrier.mk H K M E S D L T C P N)
      rw [firmNonexpansiveProjection_decode_encode_bhist H,
        firmNonexpansiveProjection_decode_encode_bhist K,
        firmNonexpansiveProjection_decode_encode_bhist M,
        firmNonexpansiveProjection_decode_encode_bhist E,
        firmNonexpansiveProjection_decode_encode_bhist S,
        firmNonexpansiveProjection_decode_encode_bhist D,
        firmNonexpansiveProjection_decode_encode_bhist L,
        firmNonexpansiveProjection_decode_encode_bhist T,
        firmNonexpansiveProjection_decode_encode_bhist C,
        firmNonexpansiveProjection_decode_encode_bhist P,
        firmNonexpansiveProjection_decode_encode_bhist N]

private theorem firmNonexpansiveProjectionToEventFlow_injective
    {x y : FirmNonexpansiveProjectionCarrier} :
    firmNonexpansiveProjectionToEventFlow x =
      firmNonexpansiveProjectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      firmNonexpansiveProjectionFromEventFlow
          (firmNonexpansiveProjectionToEventFlow x) =
        firmNonexpansiveProjectionFromEventFlow
          (firmNonexpansiveProjectionToEventFlow y) :=
    congrArg firmNonexpansiveProjectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (firmNonexpansiveProjection_round_trip x).symm
      (Eq.trans hread (firmNonexpansiveProjection_round_trip y)))

instance firmNonexpansiveProjectionBHistCarrier :
    BHistCarrier FirmNonexpansiveProjectionCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := firmNonexpansiveProjectionToEventFlow
  fromEventFlow := firmNonexpansiveProjectionFromEventFlow

instance firmNonexpansiveProjectionChapterTasteGate :
    ChapterTasteGate FirmNonexpansiveProjectionCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change firmNonexpansiveProjectionFromEventFlow
      (firmNonexpansiveProjectionToEventFlow x) = some x
    exact firmNonexpansiveProjection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (firmNonexpansiveProjectionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FirmNonexpansiveProjectionCarrier :=
  -- BEDC touchpoint anchor: BHist BMark
  firmNonexpansiveProjectionChapterTasteGate

theorem FirmNonexpansiveProjectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      firmNonexpansiveProjectionDecodeBHist
        (firmNonexpansiveProjectionEncodeBHist h) = h) ∧
      (∀ x : FirmNonexpansiveProjectionCarrier,
        firmNonexpansiveProjectionFromEventFlow
          (firmNonexpansiveProjectionToEventFlow x) = some x) ∧
        (∀ x y : FirmNonexpansiveProjectionCarrier,
          firmNonexpansiveProjectionToEventFlow x =
            firmNonexpansiveProjectionToEventFlow y → x = y) ∧
          firmNonexpansiveProjectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨firmNonexpansiveProjection_decode_encode_bhist,
      firmNonexpansiveProjection_round_trip,
      (fun _ _ heq => firmNonexpansiveProjectionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.FirmNonexpansiveProjectionUp
