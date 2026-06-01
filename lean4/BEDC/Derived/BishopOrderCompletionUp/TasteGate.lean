import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopOrderCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopOrderCompletionUp : Type where
  | mk (D S R E B L U H C P N : BHist) : BishopOrderCompletionUp
  deriving DecidableEq

def bishopOrderCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopOrderCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopOrderCompletionEncodeBHist h

def bishopOrderCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopOrderCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopOrderCompletionDecodeBHist tail)

private theorem BishopOrderCompletionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopOrderCompletionFields : BishopOrderCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopOrderCompletionUp.mk D S R E B L U H C P N => [D, S, R, E, B, L, U, H, C, P, N]

def bishopOrderCompletionToEventFlow : BishopOrderCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopOrderCompletionFields x).map bishopOrderCompletionEncodeBHist

private def BishopOrderCompletionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BishopOrderCompletionTasteGate_single_carrier_alignment_eventAt index rest

def bishopOrderCompletionFromEventFlow
    (ef : EventFlow) : Option BishopOrderCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopOrderCompletionUp.mk
      (bishopOrderCompletionDecodeBHist
        (BishopOrderCompletionTasteGate_single_carrier_alignment_eventAt 0 ef))
      (bishopOrderCompletionDecodeBHist
        (BishopOrderCompletionTasteGate_single_carrier_alignment_eventAt 1 ef))
      (bishopOrderCompletionDecodeBHist
        (BishopOrderCompletionTasteGate_single_carrier_alignment_eventAt 2 ef))
      (bishopOrderCompletionDecodeBHist
        (BishopOrderCompletionTasteGate_single_carrier_alignment_eventAt 3 ef))
      (bishopOrderCompletionDecodeBHist
        (BishopOrderCompletionTasteGate_single_carrier_alignment_eventAt 4 ef))
      (bishopOrderCompletionDecodeBHist
        (BishopOrderCompletionTasteGate_single_carrier_alignment_eventAt 5 ef))
      (bishopOrderCompletionDecodeBHist
        (BishopOrderCompletionTasteGate_single_carrier_alignment_eventAt 6 ef))
      (bishopOrderCompletionDecodeBHist
        (BishopOrderCompletionTasteGate_single_carrier_alignment_eventAt 7 ef))
      (bishopOrderCompletionDecodeBHist
        (BishopOrderCompletionTasteGate_single_carrier_alignment_eventAt 8 ef))
      (bishopOrderCompletionDecodeBHist
        (BishopOrderCompletionTasteGate_single_carrier_alignment_eventAt 9 ef))
      (bishopOrderCompletionDecodeBHist
        (BishopOrderCompletionTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem BishopOrderCompletionTasteGate_single_carrier_alignment_round_trip
    (x : BishopOrderCompletionUp) :
    bishopOrderCompletionFromEventFlow (bishopOrderCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D S R E B L U H C P N =>
      change
        some
          (BishopOrderCompletionUp.mk
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist D))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist S))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist R))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist E))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist B))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist L))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist U))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist H))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist C))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist P))
            (bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist N))) =
          some (BishopOrderCompletionUp.mk D S R E B L U H C P N)
      rw [BishopOrderCompletionTasteGate_single_carrier_alignment_decode_encode D,
        BishopOrderCompletionTasteGate_single_carrier_alignment_decode_encode S,
        BishopOrderCompletionTasteGate_single_carrier_alignment_decode_encode R,
        BishopOrderCompletionTasteGate_single_carrier_alignment_decode_encode E,
        BishopOrderCompletionTasteGate_single_carrier_alignment_decode_encode B,
        BishopOrderCompletionTasteGate_single_carrier_alignment_decode_encode L,
        BishopOrderCompletionTasteGate_single_carrier_alignment_decode_encode U,
        BishopOrderCompletionTasteGate_single_carrier_alignment_decode_encode H,
        BishopOrderCompletionTasteGate_single_carrier_alignment_decode_encode C,
        BishopOrderCompletionTasteGate_single_carrier_alignment_decode_encode P,
        BishopOrderCompletionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopOrderCompletionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopOrderCompletionUp} :
    bishopOrderCompletionToEventFlow x = bishopOrderCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopOrderCompletionFromEventFlow (bishopOrderCompletionToEventFlow x) =
        bishopOrderCompletionFromEventFlow (bishopOrderCompletionToEventFlow y) :=
    congrArg bishopOrderCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopOrderCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopOrderCompletionTasteGate_single_carrier_alignment_round_trip y)))

instance bishopOrderCompletionBHistCarrier : BHistCarrier BishopOrderCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopOrderCompletionToEventFlow
  fromEventFlow := bishopOrderCompletionFromEventFlow

instance bishopOrderCompletionChapterTasteGate :
    ChapterTasteGate BishopOrderCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopOrderCompletionFromEventFlow (bishopOrderCompletionToEventFlow x) = some x
    exact BishopOrderCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopOrderCompletionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BishopOrderCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopOrderCompletionDecodeBHist (bishopOrderCompletionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopOrderCompletionUp) ∧
        Nonempty (ChapterTasteGate BishopOrderCompletionUp) ∧
          bishopOrderCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopOrderCompletionTasteGate_single_carrier_alignment_decode_encode,
      ⟨bishopOrderCompletionBHistCarrier⟩,
      ⟨bishopOrderCompletionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BishopOrderCompletionUp
