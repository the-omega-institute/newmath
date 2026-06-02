import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopApproximationSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopApproximationSequenceUp : Type where
  | mk (D S W M R E H C P N : BHist) : BishopApproximationSequenceUp
  deriving DecidableEq

def bishopApproximationSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopApproximationSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopApproximationSequenceEncodeBHist h

def bishopApproximationSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopApproximationSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopApproximationSequenceDecodeBHist tail)

private theorem BishopApproximationSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopApproximationSequenceDecodeBHist
        (bishopApproximationSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopApproximationSequenceFields : BishopApproximationSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopApproximationSequenceUp.mk D S W M R E H C P N => [D, S, W, M, R, E, H, C, P, N]

def bishopApproximationSequenceToEventFlow : BishopApproximationSequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopApproximationSequenceFields x).map bishopApproximationSequenceEncodeBHist

private def bishopApproximationSequenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      bishopApproximationSequenceEventAtDefault index rest

def bishopApproximationSequenceFromEventFlow
    (ef : EventFlow) : Option BishopApproximationSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopApproximationSequenceUp.mk
      (bishopApproximationSequenceDecodeBHist (bishopApproximationSequenceEventAtDefault 0 ef))
      (bishopApproximationSequenceDecodeBHist (bishopApproximationSequenceEventAtDefault 1 ef))
      (bishopApproximationSequenceDecodeBHist (bishopApproximationSequenceEventAtDefault 2 ef))
      (bishopApproximationSequenceDecodeBHist (bishopApproximationSequenceEventAtDefault 3 ef))
      (bishopApproximationSequenceDecodeBHist (bishopApproximationSequenceEventAtDefault 4 ef))
      (bishopApproximationSequenceDecodeBHist (bishopApproximationSequenceEventAtDefault 5 ef))
      (bishopApproximationSequenceDecodeBHist (bishopApproximationSequenceEventAtDefault 6 ef))
      (bishopApproximationSequenceDecodeBHist (bishopApproximationSequenceEventAtDefault 7 ef))
      (bishopApproximationSequenceDecodeBHist (bishopApproximationSequenceEventAtDefault 8 ef))
      (bishopApproximationSequenceDecodeBHist (bishopApproximationSequenceEventAtDefault 9 ef)))

private theorem BishopApproximationSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopApproximationSequenceUp,
      bishopApproximationSequenceFromEventFlow
        (bishopApproximationSequenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S W M R E H C P N =>
      change
        some
          (BishopApproximationSequenceUp.mk
            (bishopApproximationSequenceDecodeBHist
              (bishopApproximationSequenceEncodeBHist D))
            (bishopApproximationSequenceDecodeBHist
              (bishopApproximationSequenceEncodeBHist S))
            (bishopApproximationSequenceDecodeBHist
              (bishopApproximationSequenceEncodeBHist W))
            (bishopApproximationSequenceDecodeBHist
              (bishopApproximationSequenceEncodeBHist M))
            (bishopApproximationSequenceDecodeBHist
              (bishopApproximationSequenceEncodeBHist R))
            (bishopApproximationSequenceDecodeBHist
              (bishopApproximationSequenceEncodeBHist E))
            (bishopApproximationSequenceDecodeBHist
              (bishopApproximationSequenceEncodeBHist H))
            (bishopApproximationSequenceDecodeBHist
              (bishopApproximationSequenceEncodeBHist C))
            (bishopApproximationSequenceDecodeBHist
              (bishopApproximationSequenceEncodeBHist P))
            (bishopApproximationSequenceDecodeBHist
              (bishopApproximationSequenceEncodeBHist N))) =
          some (BishopApproximationSequenceUp.mk D S W M R E H C P N)
      rw [BishopApproximationSequenceTasteGate_single_carrier_alignment_decode D,
        BishopApproximationSequenceTasteGate_single_carrier_alignment_decode S,
        BishopApproximationSequenceTasteGate_single_carrier_alignment_decode W,
        BishopApproximationSequenceTasteGate_single_carrier_alignment_decode M,
        BishopApproximationSequenceTasteGate_single_carrier_alignment_decode R,
        BishopApproximationSequenceTasteGate_single_carrier_alignment_decode E,
        BishopApproximationSequenceTasteGate_single_carrier_alignment_decode H,
        BishopApproximationSequenceTasteGate_single_carrier_alignment_decode C,
        BishopApproximationSequenceTasteGate_single_carrier_alignment_decode P,
        BishopApproximationSequenceTasteGate_single_carrier_alignment_decode N]

private theorem BishopApproximationSequenceTasteGate_single_carrier_alignment_injective
    {x y : BishopApproximationSequenceUp} :
    bishopApproximationSequenceToEventFlow x =
      bishopApproximationSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopApproximationSequenceFromEventFlow
          (bishopApproximationSequenceToEventFlow x) =
        bishopApproximationSequenceFromEventFlow
          (bishopApproximationSequenceToEventFlow y) :=
    congrArg bishopApproximationSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopApproximationSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopApproximationSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance bishopApproximationSequenceBHistCarrier :
    BHistCarrier BishopApproximationSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopApproximationSequenceToEventFlow
  fromEventFlow := bishopApproximationSequenceFromEventFlow

instance bishopApproximationSequenceChapterTasteGate :
    ChapterTasteGate BishopApproximationSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopApproximationSequenceFromEventFlow
        (bishopApproximationSequenceToEventFlow x) = some x
    exact BishopApproximationSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopApproximationSequenceTasteGate_single_carrier_alignment_injective heq)

instance bishopApproximationSequenceNontrivial :
    Nontrivial BishopApproximationSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopApproximationSequenceUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BishopApproximationSequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopApproximationSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopApproximationSequenceChapterTasteGate

theorem BishopApproximationSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopApproximationSequenceDecodeBHist
        (bishopApproximationSequenceEncodeBHist h) = h) ∧
      (∀ x : BishopApproximationSequenceUp,
        bishopApproximationSequenceFromEventFlow
          (bishopApproximationSequenceToEventFlow x) = some x) ∧
        (∀ x y : BishopApproximationSequenceUp,
          bishopApproximationSequenceToEventFlow x =
            bishopApproximationSequenceToEventFlow y → x = y) ∧
          bishopApproximationSequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Nontrivial
  exact
    ⟨BishopApproximationSequenceTasteGate_single_carrier_alignment_decode,
      BishopApproximationSequenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        BishopApproximationSequenceTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.BishopApproximationSequenceUp
