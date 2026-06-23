import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealChoiceSequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealChoiceSequenceUp : Type where
  | mk (L S D R E B H C P N : BHist) : LocatedRealChoiceSequenceUp
  deriving DecidableEq

def locatedRealChoiceSequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealChoiceSequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealChoiceSequenceEncodeBHist h

def locatedRealChoiceSequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealChoiceSequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealChoiceSequenceDecodeBHist tail)

private theorem LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealChoiceSequenceFields : LocatedRealChoiceSequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealChoiceSequenceUp.mk L S D R E B H C P N => [L, S, D, R, E, B, H, C, P, N]

def locatedRealChoiceSequenceToEventFlow : LocatedRealChoiceSequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedRealChoiceSequenceFields x).map locatedRealChoiceSequenceEncodeBHist

private def locatedRealChoiceSequenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedRealChoiceSequenceRawAt index rest

def locatedRealChoiceSequenceFromEventFlow (flow : EventFlow) :
    Option LocatedRealChoiceSequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedRealChoiceSequenceUp.mk
      (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceRawAt 0 flow))
      (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceRawAt 1 flow))
      (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceRawAt 2 flow))
      (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceRawAt 3 flow))
      (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceRawAt 4 flow))
      (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceRawAt 5 flow))
      (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceRawAt 6 flow))
      (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceRawAt 7 flow))
      (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceRawAt 8 flow))
      (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceRawAt 9 flow)))

private theorem LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedRealChoiceSequenceUp,
      locatedRealChoiceSequenceFromEventFlow (locatedRealChoiceSequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L S D R E B H C P N =>
      change
        some
          (LocatedRealChoiceSequenceUp.mk
            (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceEncodeBHist L))
            (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceEncodeBHist S))
            (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceEncodeBHist D))
            (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceEncodeBHist R))
            (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceEncodeBHist E))
            (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceEncodeBHist B))
            (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceEncodeBHist H))
            (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceEncodeBHist C))
            (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceEncodeBHist P))
            (locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceEncodeBHist N))) =
          some (LocatedRealChoiceSequenceUp.mk L S D R E B H C P N)
      rw [LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_decode L,
        LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_decode S,
        LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_decode D,
        LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_decode R,
        LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_decode E,
        LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_decode B,
        LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_decode H,
        LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_decode C,
        LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_decode P,
        LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_decode N]

private theorem locatedRealChoiceSequenceToEventFlow_injective
    {x y : LocatedRealChoiceSequenceUp} :
    locatedRealChoiceSequenceToEventFlow x = locatedRealChoiceSequenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealChoiceSequenceFromEventFlow (locatedRealChoiceSequenceToEventFlow x) =
        locatedRealChoiceSequenceFromEventFlow (locatedRealChoiceSequenceToEventFlow y) :=
    congrArg locatedRealChoiceSequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_round_trip y)))

instance locatedRealChoiceSequenceBHistCarrier : BHistCarrier LocatedRealChoiceSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealChoiceSequenceToEventFlow
  fromEventFlow := locatedRealChoiceSequenceFromEventFlow

instance locatedRealChoiceSequenceChapterTasteGate :
    ChapterTasteGate LocatedRealChoiceSequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedRealChoiceSequenceFromEventFlow (locatedRealChoiceSequenceToEventFlow x) =
        some x
    exact LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealChoiceSequenceToEventFlow_injective heq)

theorem LocatedRealChoiceSequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedRealChoiceSequenceDecodeBHist (locatedRealChoiceSequenceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LocatedRealChoiceSequenceUp) ∧
        Nonempty (ChapterTasteGate LocatedRealChoiceSequenceUp) ∧
          locatedRealChoiceSequenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LocatedRealChoiceSequenceTasteGate_single_carrier_alignment_decode,
      ⟨locatedRealChoiceSequenceBHistCarrier⟩,
      ⟨locatedRealChoiceSequenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LocatedRealChoiceSequenceUp
