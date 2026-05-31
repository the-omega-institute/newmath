import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedVariationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedVariationUp : Type where
  | mk (I Pi X D V R H C P N : BHist) : BoundedVariationUp
  deriving DecidableEq

def boundedVariationEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedVariationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedVariationEncodeBHist h

def boundedVariationDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedVariationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedVariationDecodeBHist tail)

private theorem BoundedVariationTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, boundedVariationDecodeBHist (boundedVariationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedVariationFields : BoundedVariationUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedVariationUp.mk I Pi X D V R H C P N => [I, Pi, X, D, V, R, H, C, P, N]

def boundedVariationToEventFlow : BoundedVariationUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (boundedVariationFields x).map boundedVariationEncodeBHist

private def boundedVariationEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedVariationEventAt index rest

def boundedVariationFromEventFlow (ef : EventFlow) : Option BoundedVariationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedVariationUp.mk
      (boundedVariationDecodeBHist (boundedVariationEventAt 0 ef))
      (boundedVariationDecodeBHist (boundedVariationEventAt 1 ef))
      (boundedVariationDecodeBHist (boundedVariationEventAt 2 ef))
      (boundedVariationDecodeBHist (boundedVariationEventAt 3 ef))
      (boundedVariationDecodeBHist (boundedVariationEventAt 4 ef))
      (boundedVariationDecodeBHist (boundedVariationEventAt 5 ef))
      (boundedVariationDecodeBHist (boundedVariationEventAt 6 ef))
      (boundedVariationDecodeBHist (boundedVariationEventAt 7 ef))
      (boundedVariationDecodeBHist (boundedVariationEventAt 8 ef))
      (boundedVariationDecodeBHist (boundedVariationEventAt 9 ef)))

private theorem BoundedVariationTasteGate_single_carrier_alignment_round_trip
    (x : BoundedVariationUp) :
    boundedVariationFromEventFlow (boundedVariationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I Pi X D V R H C P N =>
      change
        some
          (BoundedVariationUp.mk
            (boundedVariationDecodeBHist (boundedVariationEncodeBHist I))
            (boundedVariationDecodeBHist (boundedVariationEncodeBHist Pi))
            (boundedVariationDecodeBHist (boundedVariationEncodeBHist X))
            (boundedVariationDecodeBHist (boundedVariationEncodeBHist D))
            (boundedVariationDecodeBHist (boundedVariationEncodeBHist V))
            (boundedVariationDecodeBHist (boundedVariationEncodeBHist R))
            (boundedVariationDecodeBHist (boundedVariationEncodeBHist H))
            (boundedVariationDecodeBHist (boundedVariationEncodeBHist C))
            (boundedVariationDecodeBHist (boundedVariationEncodeBHist P))
            (boundedVariationDecodeBHist (boundedVariationEncodeBHist N))) =
          some (BoundedVariationUp.mk I Pi X D V R H C P N)
      rw [BoundedVariationTasteGate_single_carrier_alignment_decode_encode I,
        BoundedVariationTasteGate_single_carrier_alignment_decode_encode Pi,
        BoundedVariationTasteGate_single_carrier_alignment_decode_encode X,
        BoundedVariationTasteGate_single_carrier_alignment_decode_encode D,
        BoundedVariationTasteGate_single_carrier_alignment_decode_encode V,
        BoundedVariationTasteGate_single_carrier_alignment_decode_encode R,
        BoundedVariationTasteGate_single_carrier_alignment_decode_encode H,
        BoundedVariationTasteGate_single_carrier_alignment_decode_encode C,
        BoundedVariationTasteGate_single_carrier_alignment_decode_encode P,
        BoundedVariationTasteGate_single_carrier_alignment_decode_encode N]

private theorem BoundedVariationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedVariationUp} :
    boundedVariationToEventFlow x = boundedVariationToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedVariationFromEventFlow (boundedVariationToEventFlow x) =
        boundedVariationFromEventFlow (boundedVariationToEventFlow y) :=
    congrArg boundedVariationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedVariationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BoundedVariationTasteGate_single_carrier_alignment_round_trip y)))

instance boundedVariationBHistCarrier : BHistCarrier BoundedVariationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedVariationToEventFlow
  fromEventFlow := boundedVariationFromEventFlow

instance boundedVariationChapterTasteGate : ChapterTasteGate BoundedVariationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedVariationFromEventFlow (boundedVariationToEventFlow x) = some x
    exact BoundedVariationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BoundedVariationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate BoundedVariationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedVariationChapterTasteGate

theorem BoundedVariationTasteGate_single_carrier_alignment :
    (forall h : BHist, boundedVariationDecodeBHist (boundedVariationEncodeBHist h) = h) /\
      Nonempty (BHistCarrier BoundedVariationUp) /\
        Nonempty (ChapterTasteGate BoundedVariationUp) /\
          boundedVariationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BoundedVariationTasteGate_single_carrier_alignment_decode_encode,
      ⟨boundedVariationBHistCarrier⟩, ⟨boundedVariationChapterTasteGate⟩, rfl⟩

end BEDC.Derived.BoundedVariationUp
