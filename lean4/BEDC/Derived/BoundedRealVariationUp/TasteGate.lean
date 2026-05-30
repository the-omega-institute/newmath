import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedRealVariationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedRealVariationUp : Type where
  | mk (I Pi E R D B H C P N : BHist) : BoundedRealVariationUp
  deriving DecidableEq

def boundedRealVariationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedRealVariationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedRealVariationEncodeBHist h

def boundedRealVariationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedRealVariationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedRealVariationDecodeBHist tail)

private theorem boundedRealVariation_decode_encode_bhist :
    ∀ h : BHist,
      boundedRealVariationDecodeBHist (boundedRealVariationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def boundedRealVariationNthRawEvent : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => boundedRealVariationNthRawEvent tail n

def boundedRealVariationToEventFlow : BoundedRealVariationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRealVariationUp.mk I Pi E R D B H C P N =>
      [boundedRealVariationEncodeBHist I,
        boundedRealVariationEncodeBHist Pi,
        boundedRealVariationEncodeBHist E,
        boundedRealVariationEncodeBHist R,
        boundedRealVariationEncodeBHist D,
        boundedRealVariationEncodeBHist B,
        boundedRealVariationEncodeBHist H,
        boundedRealVariationEncodeBHist C,
        boundedRealVariationEncodeBHist P,
        boundedRealVariationEncodeBHist N]

def boundedRealVariationFromEventFlow (ef : EventFlow) : Option BoundedRealVariationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedRealVariationUp.mk
      (boundedRealVariationDecodeBHist (boundedRealVariationNthRawEvent ef 0))
      (boundedRealVariationDecodeBHist (boundedRealVariationNthRawEvent ef 1))
      (boundedRealVariationDecodeBHist (boundedRealVariationNthRawEvent ef 2))
      (boundedRealVariationDecodeBHist (boundedRealVariationNthRawEvent ef 3))
      (boundedRealVariationDecodeBHist (boundedRealVariationNthRawEvent ef 4))
      (boundedRealVariationDecodeBHist (boundedRealVariationNthRawEvent ef 5))
      (boundedRealVariationDecodeBHist (boundedRealVariationNthRawEvent ef 6))
      (boundedRealVariationDecodeBHist (boundedRealVariationNthRawEvent ef 7))
      (boundedRealVariationDecodeBHist (boundedRealVariationNthRawEvent ef 8))
      (boundedRealVariationDecodeBHist (boundedRealVariationNthRawEvent ef 9)))

private theorem boundedRealVariation_round_trip :
    ∀ x : BoundedRealVariationUp,
      boundedRealVariationFromEventFlow (boundedRealVariationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I Pi E R D B H C P N =>
      change
        some
          (BoundedRealVariationUp.mk
            (boundedRealVariationDecodeBHist (boundedRealVariationEncodeBHist I))
            (boundedRealVariationDecodeBHist (boundedRealVariationEncodeBHist Pi))
            (boundedRealVariationDecodeBHist (boundedRealVariationEncodeBHist E))
            (boundedRealVariationDecodeBHist (boundedRealVariationEncodeBHist R))
            (boundedRealVariationDecodeBHist (boundedRealVariationEncodeBHist D))
            (boundedRealVariationDecodeBHist (boundedRealVariationEncodeBHist B))
            (boundedRealVariationDecodeBHist (boundedRealVariationEncodeBHist H))
            (boundedRealVariationDecodeBHist (boundedRealVariationEncodeBHist C))
            (boundedRealVariationDecodeBHist (boundedRealVariationEncodeBHist P))
            (boundedRealVariationDecodeBHist (boundedRealVariationEncodeBHist N))) =
          some (BoundedRealVariationUp.mk I Pi E R D B H C P N)
      rw [boundedRealVariation_decode_encode_bhist I,
        boundedRealVariation_decode_encode_bhist Pi,
        boundedRealVariation_decode_encode_bhist E,
        boundedRealVariation_decode_encode_bhist R,
        boundedRealVariation_decode_encode_bhist D,
        boundedRealVariation_decode_encode_bhist B,
        boundedRealVariation_decode_encode_bhist H,
        boundedRealVariation_decode_encode_bhist C,
        boundedRealVariation_decode_encode_bhist P,
        boundedRealVariation_decode_encode_bhist N]

private theorem boundedRealVariationToEventFlow_injective
    {x y : BoundedRealVariationUp} :
    boundedRealVariationToEventFlow x = boundedRealVariationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedRealVariationFromEventFlow (boundedRealVariationToEventFlow x) =
        boundedRealVariationFromEventFlow (boundedRealVariationToEventFlow y) :=
    congrArg boundedRealVariationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundedRealVariation_round_trip x).symm
      (Eq.trans hread (boundedRealVariation_round_trip y)))

instance boundedRealVariationBHistCarrier : BHistCarrier BoundedRealVariationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedRealVariationToEventFlow
  fromEventFlow := boundedRealVariationFromEventFlow

instance boundedRealVariationChapterTasteGate : ChapterTasteGate BoundedRealVariationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedRealVariationFromEventFlow (boundedRealVariationToEventFlow x) = some x
    exact boundedRealVariation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedRealVariationToEventFlow_injective heq)

theorem BoundedRealVariationTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BoundedRealVariationUp) ∧
      Nonempty (ChapterTasteGate BoundedRealVariationUp) ∧
        (∀ h : BHist, boundedRealVariationDecodeBHist
          (boundedRealVariationEncodeBHist h) = h) ∧
          boundedRealVariationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨⟨boundedRealVariationBHistCarrier⟩,
      ⟨boundedRealVariationChapterTasteGate⟩,
      boundedRealVariation_decode_encode_bhist,
      rfl⟩

end BEDC.Derived.BoundedRealVariationUp
