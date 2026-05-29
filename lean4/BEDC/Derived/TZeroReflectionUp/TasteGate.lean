import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TZeroReflectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TZeroReflectionUp : Type where
  | mk (T S R Q H C P N : BHist) : TZeroReflectionUp
  deriving DecidableEq

def tZeroReflectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tZeroReflectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tZeroReflectionEncodeBHist h

def tZeroReflectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tZeroReflectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tZeroReflectionDecodeBHist tail)

private theorem TZeroReflectionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, tZeroReflectionDecodeBHist (tZeroReflectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def tZeroReflectionToEventFlow : TZeroReflectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TZeroReflectionUp.mk T S R Q H C P N =>
      [[BMark.b0],
        tZeroReflectionEncodeBHist T,
        [BMark.b1, BMark.b0],
        tZeroReflectionEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        tZeroReflectionEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tZeroReflectionEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tZeroReflectionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tZeroReflectionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tZeroReflectionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        tZeroReflectionEncodeBHist N]

private def tZeroReflectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => tZeroReflectionEventAtDefault index rest

def tZeroReflectionFromEventFlow (ef : EventFlow) : Option TZeroReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TZeroReflectionUp.mk
      (tZeroReflectionDecodeBHist (tZeroReflectionEventAtDefault 1 ef))
      (tZeroReflectionDecodeBHist (tZeroReflectionEventAtDefault 3 ef))
      (tZeroReflectionDecodeBHist (tZeroReflectionEventAtDefault 5 ef))
      (tZeroReflectionDecodeBHist (tZeroReflectionEventAtDefault 7 ef))
      (tZeroReflectionDecodeBHist (tZeroReflectionEventAtDefault 9 ef))
      (tZeroReflectionDecodeBHist (tZeroReflectionEventAtDefault 11 ef))
      (tZeroReflectionDecodeBHist (tZeroReflectionEventAtDefault 13 ef))
      (tZeroReflectionDecodeBHist (tZeroReflectionEventAtDefault 15 ef)))

private theorem TZeroReflectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TZeroReflectionUp,
      tZeroReflectionFromEventFlow (tZeroReflectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T S R Q H C P N =>
      change
        some
          (TZeroReflectionUp.mk
            (tZeroReflectionDecodeBHist (tZeroReflectionEncodeBHist T))
            (tZeroReflectionDecodeBHist (tZeroReflectionEncodeBHist S))
            (tZeroReflectionDecodeBHist (tZeroReflectionEncodeBHist R))
            (tZeroReflectionDecodeBHist (tZeroReflectionEncodeBHist Q))
            (tZeroReflectionDecodeBHist (tZeroReflectionEncodeBHist H))
            (tZeroReflectionDecodeBHist (tZeroReflectionEncodeBHist C))
            (tZeroReflectionDecodeBHist (tZeroReflectionEncodeBHist P))
            (tZeroReflectionDecodeBHist (tZeroReflectionEncodeBHist N))) =
          some (TZeroReflectionUp.mk T S R Q H C P N)
      rw [TZeroReflectionTasteGate_single_carrier_alignment_decode_encode T,
        TZeroReflectionTasteGate_single_carrier_alignment_decode_encode S,
        TZeroReflectionTasteGate_single_carrier_alignment_decode_encode R,
        TZeroReflectionTasteGate_single_carrier_alignment_decode_encode Q,
        TZeroReflectionTasteGate_single_carrier_alignment_decode_encode H,
        TZeroReflectionTasteGate_single_carrier_alignment_decode_encode C,
        TZeroReflectionTasteGate_single_carrier_alignment_decode_encode P,
        TZeroReflectionTasteGate_single_carrier_alignment_decode_encode N]

private theorem TZeroReflectionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TZeroReflectionUp} :
    tZeroReflectionToEventFlow x = tZeroReflectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tZeroReflectionFromEventFlow (tZeroReflectionToEventFlow x) =
        tZeroReflectionFromEventFlow (tZeroReflectionToEventFlow y) :=
    congrArg tZeroReflectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TZeroReflectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TZeroReflectionTasteGate_single_carrier_alignment_round_trip y)))

instance tZeroReflectionBHistCarrier : BHistCarrier TZeroReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tZeroReflectionToEventFlow
  fromEventFlow := tZeroReflectionFromEventFlow

instance tZeroReflectionChapterTasteGate : ChapterTasteGate TZeroReflectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tZeroReflectionFromEventFlow (tZeroReflectionToEventFlow x) = some x
    exact TZeroReflectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TZeroReflectionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate TZeroReflectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tZeroReflectionChapterTasteGate

theorem TZeroReflectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, tZeroReflectionDecodeBHist (tZeroReflectionEncodeBHist h) = h) ∧
      (∀ x : TZeroReflectionUp,
        tZeroReflectionFromEventFlow (tZeroReflectionToEventFlow x) = some x) ∧
        (∀ x y : TZeroReflectionUp,
          tZeroReflectionToEventFlow x = tZeroReflectionToEventFlow y → x = y) ∧
          tZeroReflectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨TZeroReflectionTasteGate_single_carrier_alignment_decode_encode,
      TZeroReflectionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => TZeroReflectionTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.TZeroReflectionUp
