import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CousinCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CousinCoverUp : Type where
  | mk
      (interval gauge taggedCells mesh windows readback realSeal transport replay provenance
        name : BHist) : CousinCoverUp
  deriving DecidableEq

def cousinCoverEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cousinCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cousinCoverEncodeBHist h

def cousinCoverDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cousinCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cousinCoverDecodeBHist tail)

private theorem cousinCover_decode_encode :
    forall h : BHist, cousinCoverDecodeBHist (cousinCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cousinCoverToEventFlow : CousinCoverUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CousinCoverUp.mk interval gauge taggedCells mesh windows readback realSeal transport replay
      provenance name =>
      [[BMark.b0],
        cousinCoverEncodeBHist interval,
        [BMark.b1],
        cousinCoverEncodeBHist gauge,
        [BMark.b0, BMark.b0],
        cousinCoverEncodeBHist taggedCells,
        [BMark.b0, BMark.b1],
        cousinCoverEncodeBHist mesh,
        [BMark.b1, BMark.b0],
        cousinCoverEncodeBHist windows,
        [BMark.b1, BMark.b1],
        cousinCoverEncodeBHist readback,
        [BMark.b0, BMark.b0, BMark.b0],
        cousinCoverEncodeBHist realSeal,
        [BMark.b0, BMark.b0, BMark.b1],
        cousinCoverEncodeBHist transport,
        [BMark.b0, BMark.b1, BMark.b0],
        cousinCoverEncodeBHist replay,
        [BMark.b0, BMark.b1, BMark.b1],
        cousinCoverEncodeBHist provenance,
        [BMark.b1, BMark.b0, BMark.b0],
        cousinCoverEncodeBHist name]

private def cousinCoverEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => cousinCoverEventAtDefault index rest

def cousinCoverFromEventFlow : EventFlow -> Option CousinCoverUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (CousinCoverUp.mk
          (cousinCoverDecodeBHist (cousinCoverEventAtDefault 1 flow))
          (cousinCoverDecodeBHist (cousinCoverEventAtDefault 3 flow))
          (cousinCoverDecodeBHist (cousinCoverEventAtDefault 5 flow))
          (cousinCoverDecodeBHist (cousinCoverEventAtDefault 7 flow))
          (cousinCoverDecodeBHist (cousinCoverEventAtDefault 9 flow))
          (cousinCoverDecodeBHist (cousinCoverEventAtDefault 11 flow))
          (cousinCoverDecodeBHist (cousinCoverEventAtDefault 13 flow))
          (cousinCoverDecodeBHist (cousinCoverEventAtDefault 15 flow))
          (cousinCoverDecodeBHist (cousinCoverEventAtDefault 17 flow))
          (cousinCoverDecodeBHist (cousinCoverEventAtDefault 19 flow))
          (cousinCoverDecodeBHist (cousinCoverEventAtDefault 21 flow)))

private theorem cousinCover_round_trip :
    forall x : CousinCoverUp,
      cousinCoverFromEventFlow (cousinCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk interval gauge taggedCells mesh windows readback realSeal transport replay provenance name =>
      change
        some
          (CousinCoverUp.mk
            (cousinCoverDecodeBHist (cousinCoverEncodeBHist interval))
            (cousinCoverDecodeBHist (cousinCoverEncodeBHist gauge))
            (cousinCoverDecodeBHist (cousinCoverEncodeBHist taggedCells))
            (cousinCoverDecodeBHist (cousinCoverEncodeBHist mesh))
            (cousinCoverDecodeBHist (cousinCoverEncodeBHist windows))
            (cousinCoverDecodeBHist (cousinCoverEncodeBHist readback))
            (cousinCoverDecodeBHist (cousinCoverEncodeBHist realSeal))
            (cousinCoverDecodeBHist (cousinCoverEncodeBHist transport))
            (cousinCoverDecodeBHist (cousinCoverEncodeBHist replay))
            (cousinCoverDecodeBHist (cousinCoverEncodeBHist provenance))
            (cousinCoverDecodeBHist (cousinCoverEncodeBHist name))) =
          some
            (CousinCoverUp.mk interval gauge taggedCells mesh windows readback realSeal transport
              replay provenance name)
      rw [cousinCover_decode_encode interval,
        cousinCover_decode_encode gauge,
        cousinCover_decode_encode taggedCells,
        cousinCover_decode_encode mesh,
        cousinCover_decode_encode windows,
        cousinCover_decode_encode readback,
        cousinCover_decode_encode realSeal,
        cousinCover_decode_encode transport,
        cousinCover_decode_encode replay,
        cousinCover_decode_encode provenance,
        cousinCover_decode_encode name]

private theorem cousinCoverToEventFlow_injective {x y : CousinCoverUp} :
    cousinCoverToEventFlow x = cousinCoverToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cousinCoverFromEventFlow (cousinCoverToEventFlow x) =
        cousinCoverFromEventFlow (cousinCoverToEventFlow y) :=
    congrArg cousinCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cousinCover_round_trip x).symm
      (Eq.trans hread (cousinCover_round_trip y)))

instance cousinCoverBHistCarrier : BHistCarrier CousinCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cousinCoverToEventFlow
  fromEventFlow := cousinCoverFromEventFlow

instance cousinCoverChapterTasteGate : ChapterTasteGate CousinCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cousinCoverFromEventFlow (cousinCoverToEventFlow x) = some x
    exact cousinCover_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cousinCoverToEventFlow_injective heq)

theorem CousinCoverTasteGate_single_carrier_alignment :
    (forall h : BHist, cousinCoverDecodeBHist (cousinCoverEncodeBHist h) = h) /\
      (forall x : CousinCoverUp, cousinCoverFromEventFlow (cousinCoverToEventFlow x) = some x) /\
      (forall x y : CousinCoverUp,
        cousinCoverToEventFlow x = cousinCoverToEventFlow y -> x = y) /\
      cousinCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cousinCover_decode_encode,
      cousinCover_round_trip,
      (fun _ _ heq => cousinCoverToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CousinCoverUp
