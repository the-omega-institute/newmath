import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedNormalizationCandidateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedNormalizationCandidateUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (T F E A Pi S I R H C P N : BHist) : BoundedNormalizationCandidateUp
  deriving DecidableEq

def boundedNormalizationCandidateEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedNormalizationCandidateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedNormalizationCandidateEncodeBHist h

def boundedNormalizationCandidateDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedNormalizationCandidateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedNormalizationCandidateDecodeBHist tail)

private theorem BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      boundedNormalizationCandidateDecodeBHist
        (boundedNormalizationCandidateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedNormalizationCandidateFields :
    BoundedNormalizationCandidateUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedNormalizationCandidateUp.mk T F E A Pi S I R H C P N =>
      [T, F, E, A, Pi, S, I, R, H, C, P, N]

def boundedNormalizationCandidateToEventFlow :
    BoundedNormalizationCandidateUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (boundedNormalizationCandidateFields x).map boundedNormalizationCandidateEncodeBHist

private def boundedNormalizationCandidateEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedNormalizationCandidateEventAtDefault index rest

def boundedNormalizationCandidateFromEventFlow
    (ef : EventFlow) : Option BoundedNormalizationCandidateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedNormalizationCandidateUp.mk
      (boundedNormalizationCandidateDecodeBHist (boundedNormalizationCandidateEventAtDefault 0 ef))
      (boundedNormalizationCandidateDecodeBHist (boundedNormalizationCandidateEventAtDefault 1 ef))
      (boundedNormalizationCandidateDecodeBHist (boundedNormalizationCandidateEventAtDefault 2 ef))
      (boundedNormalizationCandidateDecodeBHist (boundedNormalizationCandidateEventAtDefault 3 ef))
      (boundedNormalizationCandidateDecodeBHist (boundedNormalizationCandidateEventAtDefault 4 ef))
      (boundedNormalizationCandidateDecodeBHist (boundedNormalizationCandidateEventAtDefault 5 ef))
      (boundedNormalizationCandidateDecodeBHist (boundedNormalizationCandidateEventAtDefault 6 ef))
      (boundedNormalizationCandidateDecodeBHist (boundedNormalizationCandidateEventAtDefault 7 ef))
      (boundedNormalizationCandidateDecodeBHist (boundedNormalizationCandidateEventAtDefault 8 ef))
      (boundedNormalizationCandidateDecodeBHist (boundedNormalizationCandidateEventAtDefault 9 ef))
      (boundedNormalizationCandidateDecodeBHist (boundedNormalizationCandidateEventAtDefault 10 ef))
      (boundedNormalizationCandidateDecodeBHist (boundedNormalizationCandidateEventAtDefault 11 ef)))

private theorem BoundedNormalizationCandidateTasteGate_single_carrier_alignment_round_trip :
    forall x : BoundedNormalizationCandidateUp,
      boundedNormalizationCandidateFromEventFlow
        (boundedNormalizationCandidateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T F E A Pi S I R H C P N =>
      change
        some
          (BoundedNormalizationCandidateUp.mk
            (boundedNormalizationCandidateDecodeBHist
              (boundedNormalizationCandidateEncodeBHist T))
            (boundedNormalizationCandidateDecodeBHist
              (boundedNormalizationCandidateEncodeBHist F))
            (boundedNormalizationCandidateDecodeBHist
              (boundedNormalizationCandidateEncodeBHist E))
            (boundedNormalizationCandidateDecodeBHist
              (boundedNormalizationCandidateEncodeBHist A))
            (boundedNormalizationCandidateDecodeBHist
              (boundedNormalizationCandidateEncodeBHist Pi))
            (boundedNormalizationCandidateDecodeBHist
              (boundedNormalizationCandidateEncodeBHist S))
            (boundedNormalizationCandidateDecodeBHist
              (boundedNormalizationCandidateEncodeBHist I))
            (boundedNormalizationCandidateDecodeBHist
              (boundedNormalizationCandidateEncodeBHist R))
            (boundedNormalizationCandidateDecodeBHist
              (boundedNormalizationCandidateEncodeBHist H))
            (boundedNormalizationCandidateDecodeBHist
              (boundedNormalizationCandidateEncodeBHist C))
            (boundedNormalizationCandidateDecodeBHist
              (boundedNormalizationCandidateEncodeBHist P))
            (boundedNormalizationCandidateDecodeBHist
              (boundedNormalizationCandidateEncodeBHist N))) =
          some (BoundedNormalizationCandidateUp.mk T F E A Pi S I R H C P N)
      rw [BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode T,
        BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode F,
        BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode E,
        BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode A,
        BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode Pi,
        BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode S,
        BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode I,
        BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode R,
        BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode H,
        BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode C,
        BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode P,
        BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode N]

private theorem BoundedNormalizationCandidateTasteGate_single_carrier_alignment_injective
    {x y : BoundedNormalizationCandidateUp} :
    boundedNormalizationCandidateToEventFlow x =
      boundedNormalizationCandidateToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedNormalizationCandidateFromEventFlow
          (boundedNormalizationCandidateToEventFlow x) =
        boundedNormalizationCandidateFromEventFlow
          (boundedNormalizationCandidateToEventFlow y) :=
    congrArg boundedNormalizationCandidateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedNormalizationCandidateTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedNormalizationCandidateTasteGate_single_carrier_alignment_round_trip y)))

instance boundedNormalizationCandidateBHistCarrier :
    BHistCarrier BoundedNormalizationCandidateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedNormalizationCandidateToEventFlow
  fromEventFlow := boundedNormalizationCandidateFromEventFlow

instance boundedNormalizationCandidateChapterTasteGate :
    ChapterTasteGate BoundedNormalizationCandidateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      boundedNormalizationCandidateFromEventFlow
          (boundedNormalizationCandidateToEventFlow x) =
        some x
    exact BoundedNormalizationCandidateTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedNormalizationCandidateTasteGate_single_carrier_alignment_injective heq)

theorem BoundedNormalizationCandidateTasteGate_single_carrier_alignment :
    (forall h : BHist,
      boundedNormalizationCandidateDecodeBHist
        (boundedNormalizationCandidateEncodeBHist h) = h) /\
      Nonempty (BHistCarrier BoundedNormalizationCandidateUp) /\
        Nonempty (ChapterTasteGate BoundedNormalizationCandidateUp) /\
          boundedNormalizationCandidateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BoundedNormalizationCandidateTasteGate_single_carrier_alignment_decode,
      ⟨boundedNormalizationCandidateBHistCarrier⟩,
      ⟨boundedNormalizationCandidateChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BoundedNormalizationCandidateUp
