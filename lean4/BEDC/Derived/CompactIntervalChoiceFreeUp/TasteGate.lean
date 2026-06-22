import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactIntervalChoiceFreeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactIntervalChoiceFreeUp : Type where
  | mk (E D S Q R T C P N : BHist) : CompactIntervalChoiceFreeUp
  deriving DecidableEq

def compactIntervalChoiceFreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactIntervalChoiceFreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactIntervalChoiceFreeEncodeBHist h

def compactIntervalChoiceFreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactIntervalChoiceFreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactIntervalChoiceFreeDecodeBHist tail)

private theorem CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactIntervalChoiceFreeFields : CompactIntervalChoiceFreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactIntervalChoiceFreeUp.mk E D S Q R T C P N => [E, D, S, Q, R, T, C, P, N]

def compactIntervalChoiceFreeToEventFlow : CompactIntervalChoiceFreeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactIntervalChoiceFreeFields x).map compactIntervalChoiceFreeEncodeBHist

private def compactIntervalChoiceFreeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactIntervalChoiceFreeEventAt index rest

def compactIntervalChoiceFreeFromEventFlow (ef : EventFlow) :
    Option CompactIntervalChoiceFreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactIntervalChoiceFreeUp.mk
      (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEventAt 0 ef))
      (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEventAt 1 ef))
      (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEventAt 2 ef))
      (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEventAt 3 ef))
      (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEventAt 4 ef))
      (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEventAt 5 ef))
      (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEventAt 6 ef))
      (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEventAt 7 ef))
      (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEventAt 8 ef)))

private theorem CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_round_trip
    (x : CompactIntervalChoiceFreeUp) :
    compactIntervalChoiceFreeFromEventFlow (compactIntervalChoiceFreeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk E D S Q R T C P N =>
      change
        some
            (CompactIntervalChoiceFreeUp.mk
              (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEncodeBHist E))
              (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEncodeBHist D))
              (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEncodeBHist S))
              (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEncodeBHist Q))
              (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEncodeBHist R))
              (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEncodeBHist T))
              (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEncodeBHist C))
              (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEncodeBHist P))
              (compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEncodeBHist N))) =
          some (CompactIntervalChoiceFreeUp.mk E D S Q R T C P N)
      rw [CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_decode_encode E,
        CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_decode_encode D,
        CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_decode_encode S,
        CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_decode_encode Q,
        CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_decode_encode R,
        CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_decode_encode T,
        CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_decode_encode C,
        CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_decode_encode P,
        CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_decode_encode N]

private theorem CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactIntervalChoiceFreeUp} :
    compactIntervalChoiceFreeToEventFlow x = compactIntervalChoiceFreeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactIntervalChoiceFreeFromEventFlow (compactIntervalChoiceFreeToEventFlow x) =
        compactIntervalChoiceFreeFromEventFlow (compactIntervalChoiceFreeToEventFlow y) :=
    congrArg compactIntervalChoiceFreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_round_trip y)))

instance compactIntervalChoiceFreeBHistCarrier :
    BHistCarrier CompactIntervalChoiceFreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactIntervalChoiceFreeToEventFlow
  fromEventFlow := compactIntervalChoiceFreeFromEventFlow

instance compactIntervalChoiceFreeChapterTasteGate :
    ChapterTasteGate CompactIntervalChoiceFreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactIntervalChoiceFreeFromEventFlow (compactIntervalChoiceFreeToEventFlow x) = some x
    exact CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def CompactIntervalChoiceFree.taste_gate : ChapterTasteGate CompactIntervalChoiceFreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactIntervalChoiceFreeChapterTasteGate

theorem CompactIntervalChoiceFreeTasteGate_single_carrier_alignment :
    (forall h : BHist,
      compactIntervalChoiceFreeDecodeBHist (compactIntervalChoiceFreeEncodeBHist h) = h) ∧
      (forall x : CompactIntervalChoiceFreeUp,
        compactIntervalChoiceFreeFromEventFlow (compactIntervalChoiceFreeToEventFlow x) = some x) ∧
      (forall x y : CompactIntervalChoiceFreeUp,
        compactIntervalChoiceFreeToEventFlow x = compactIntervalChoiceFreeToEventFlow y -> x = y) ∧
      compactIntervalChoiceFreeFields
          (CompactIntervalChoiceFreeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_decode_encode,
      CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_round_trip,
      fun x y hxy =>
        CompactIntervalChoiceFreeTasteGate_single_carrier_alignment_toEventFlow_injective hxy,
      rfl⟩

end BEDC.Derived.CompactIntervalChoiceFreeUp.TasteGate
