import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionSeparationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionSeparationUp : Type where
  | mk (A B D W R E U H C P N : BHist) : RegularCauchyCompletionSeparationUp
  deriving DecidableEq

def regularCauchyCompletionSeparationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionSeparationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionSeparationEncodeBHist h

def regularCauchyCompletionSeparationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionSeparationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionSeparationDecodeBHist tail)

private theorem RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyCompletionSeparationDecodeBHist
        (regularCauchyCompletionSeparationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCompletionSeparationToEventFlow :
    RegularCauchyCompletionSeparationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionSeparationUp.mk A B D W R E U H C P N =>
      [[BMark.b0],
        regularCauchyCompletionSeparationEncodeBHist A,
        [BMark.b1, BMark.b0],
        regularCauchyCompletionSeparationEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionSeparationEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionSeparationEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionSeparationEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionSeparationEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionSeparationEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyCompletionSeparationEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyCompletionSeparationEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionSeparationEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyCompletionSeparationEncodeBHist N]

private def regularCauchyCompletionSeparationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyCompletionSeparationEventAtDefault index rest

def regularCauchyCompletionSeparationFromEventFlow
    (ef : EventFlow) : Option RegularCauchyCompletionSeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyCompletionSeparationUp.mk
      (regularCauchyCompletionSeparationDecodeBHist
        (regularCauchyCompletionSeparationEventAtDefault 1 ef))
      (regularCauchyCompletionSeparationDecodeBHist
        (regularCauchyCompletionSeparationEventAtDefault 3 ef))
      (regularCauchyCompletionSeparationDecodeBHist
        (regularCauchyCompletionSeparationEventAtDefault 5 ef))
      (regularCauchyCompletionSeparationDecodeBHist
        (regularCauchyCompletionSeparationEventAtDefault 7 ef))
      (regularCauchyCompletionSeparationDecodeBHist
        (regularCauchyCompletionSeparationEventAtDefault 9 ef))
      (regularCauchyCompletionSeparationDecodeBHist
        (regularCauchyCompletionSeparationEventAtDefault 11 ef))
      (regularCauchyCompletionSeparationDecodeBHist
        (regularCauchyCompletionSeparationEventAtDefault 13 ef))
      (regularCauchyCompletionSeparationDecodeBHist
        (regularCauchyCompletionSeparationEventAtDefault 15 ef))
      (regularCauchyCompletionSeparationDecodeBHist
        (regularCauchyCompletionSeparationEventAtDefault 17 ef))
      (regularCauchyCompletionSeparationDecodeBHist
        (regularCauchyCompletionSeparationEventAtDefault 19 ef))
      (regularCauchyCompletionSeparationDecodeBHist
        (regularCauchyCompletionSeparationEventAtDefault 21 ef)))

private theorem RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyCompletionSeparationUp,
      regularCauchyCompletionSeparationFromEventFlow
        (regularCauchyCompletionSeparationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B D W R E U H C P N =>
      change
        some
          (RegularCauchyCompletionSeparationUp.mk
            (regularCauchyCompletionSeparationDecodeBHist
              (regularCauchyCompletionSeparationEncodeBHist A))
            (regularCauchyCompletionSeparationDecodeBHist
              (regularCauchyCompletionSeparationEncodeBHist B))
            (regularCauchyCompletionSeparationDecodeBHist
              (regularCauchyCompletionSeparationEncodeBHist D))
            (regularCauchyCompletionSeparationDecodeBHist
              (regularCauchyCompletionSeparationEncodeBHist W))
            (regularCauchyCompletionSeparationDecodeBHist
              (regularCauchyCompletionSeparationEncodeBHist R))
            (regularCauchyCompletionSeparationDecodeBHist
              (regularCauchyCompletionSeparationEncodeBHist E))
            (regularCauchyCompletionSeparationDecodeBHist
              (regularCauchyCompletionSeparationEncodeBHist U))
            (regularCauchyCompletionSeparationDecodeBHist
              (regularCauchyCompletionSeparationEncodeBHist H))
            (regularCauchyCompletionSeparationDecodeBHist
              (regularCauchyCompletionSeparationEncodeBHist C))
            (regularCauchyCompletionSeparationDecodeBHist
              (regularCauchyCompletionSeparationEncodeBHist P))
            (regularCauchyCompletionSeparationDecodeBHist
              (regularCauchyCompletionSeparationEncodeBHist N))) =
          some (RegularCauchyCompletionSeparationUp.mk A B D W R E U H C P N)
      rw [RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_decode_encode A,
        RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_decode_encode B,
        RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_decode_encode U,
        RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyCompletionSeparationUp} :
    regularCauchyCompletionSeparationToEventFlow x =
      regularCauchyCompletionSeparationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionSeparationFromEventFlow
          (regularCauchyCompletionSeparationToEventFlow x) =
        regularCauchyCompletionSeparationFromEventFlow
          (regularCauchyCompletionSeparationToEventFlow y) :=
    congrArg regularCauchyCompletionSeparationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyCompletionSeparationBHistCarrier :
    BHistCarrier RegularCauchyCompletionSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionSeparationToEventFlow
  fromEventFlow := regularCauchyCompletionSeparationFromEventFlow

instance regularCauchyCompletionSeparationChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionSeparationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyCompletionSeparationFromEventFlow
      (regularCauchyCompletionSeparationToEventFlow x) = some x
    exact RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyCompletionSeparationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCompletionSeparationChapterTasteGate

theorem RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyCompletionSeparationDecodeBHist
        (regularCauchyCompletionSeparationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyCompletionSeparationUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyCompletionSeparationUp) ∧
          regularCauchyCompletionSeparationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyCompletionSeparationTasteGate_single_carrier_alignment_decode_encode,
      ⟨regularCauchyCompletionSeparationBHistCarrier⟩,
      ⟨regularCauchyCompletionSeparationChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyCompletionSeparationUp
