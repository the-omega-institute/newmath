import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedRealUpperCutUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedRealUpperCutUp : Type where
  | mk (R A D S O B H C P N : BHist) : BoundedRealUpperCutUp
  deriving DecidableEq

def boundedRealUpperCutEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedRealUpperCutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedRealUpperCutEncodeBHist h

def boundedRealUpperCutDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedRealUpperCutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedRealUpperCutDecodeBHist tail)

private theorem BoundedRealUpperCutTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      boundedRealUpperCutDecodeBHist (boundedRealUpperCutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedRealUpperCutFields : BoundedRealUpperCutUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRealUpperCutUp.mk R A D S O B H C P N => [R, A, D, S, O, B, H, C, P, N]

def boundedRealUpperCutToEventFlow : BoundedRealUpperCutUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map boundedRealUpperCutEncodeBHist (boundedRealUpperCutFields x)

private def boundedRealUpperCutRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedRealUpperCutRawAt index rest

def boundedRealUpperCutFromEventFlow
    (flow : EventFlow) : Option BoundedRealUpperCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedRealUpperCutUp.mk
      (boundedRealUpperCutDecodeBHist (boundedRealUpperCutRawAt 0 flow))
      (boundedRealUpperCutDecodeBHist (boundedRealUpperCutRawAt 1 flow))
      (boundedRealUpperCutDecodeBHist (boundedRealUpperCutRawAt 2 flow))
      (boundedRealUpperCutDecodeBHist (boundedRealUpperCutRawAt 3 flow))
      (boundedRealUpperCutDecodeBHist (boundedRealUpperCutRawAt 4 flow))
      (boundedRealUpperCutDecodeBHist (boundedRealUpperCutRawAt 5 flow))
      (boundedRealUpperCutDecodeBHist (boundedRealUpperCutRawAt 6 flow))
      (boundedRealUpperCutDecodeBHist (boundedRealUpperCutRawAt 7 flow))
      (boundedRealUpperCutDecodeBHist (boundedRealUpperCutRawAt 8 flow))
      (boundedRealUpperCutDecodeBHist (boundedRealUpperCutRawAt 9 flow)))

private theorem BoundedRealUpperCutTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BoundedRealUpperCutUp,
      boundedRealUpperCutFromEventFlow (boundedRealUpperCutToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R A D S O B H C P N =>
      change
        some
          (BoundedRealUpperCutUp.mk
            (boundedRealUpperCutDecodeBHist (boundedRealUpperCutEncodeBHist R))
            (boundedRealUpperCutDecodeBHist (boundedRealUpperCutEncodeBHist A))
            (boundedRealUpperCutDecodeBHist (boundedRealUpperCutEncodeBHist D))
            (boundedRealUpperCutDecodeBHist (boundedRealUpperCutEncodeBHist S))
            (boundedRealUpperCutDecodeBHist (boundedRealUpperCutEncodeBHist O))
            (boundedRealUpperCutDecodeBHist (boundedRealUpperCutEncodeBHist B))
            (boundedRealUpperCutDecodeBHist (boundedRealUpperCutEncodeBHist H))
            (boundedRealUpperCutDecodeBHist (boundedRealUpperCutEncodeBHist C))
            (boundedRealUpperCutDecodeBHist (boundedRealUpperCutEncodeBHist P))
            (boundedRealUpperCutDecodeBHist (boundedRealUpperCutEncodeBHist N))) =
          some (BoundedRealUpperCutUp.mk R A D S O B H C P N)
      rw [BoundedRealUpperCutTasteGate_single_carrier_alignment_decode R,
        BoundedRealUpperCutTasteGate_single_carrier_alignment_decode A,
        BoundedRealUpperCutTasteGate_single_carrier_alignment_decode D,
        BoundedRealUpperCutTasteGate_single_carrier_alignment_decode S,
        BoundedRealUpperCutTasteGate_single_carrier_alignment_decode O,
        BoundedRealUpperCutTasteGate_single_carrier_alignment_decode B,
        BoundedRealUpperCutTasteGate_single_carrier_alignment_decode H,
        BoundedRealUpperCutTasteGate_single_carrier_alignment_decode C,
        BoundedRealUpperCutTasteGate_single_carrier_alignment_decode P,
        BoundedRealUpperCutTasteGate_single_carrier_alignment_decode N]

private theorem boundedRealUpperCutToEventFlow_injective
    {x y : BoundedRealUpperCutUp} :
    boundedRealUpperCutToEventFlow x = boundedRealUpperCutToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedRealUpperCutFromEventFlow (boundedRealUpperCutToEventFlow x) =
        boundedRealUpperCutFromEventFlow (boundedRealUpperCutToEventFlow y) :=
    congrArg boundedRealUpperCutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BoundedRealUpperCutTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BoundedRealUpperCutTasteGate_single_carrier_alignment_round_trip y)))

instance boundedRealUpperCutBHistCarrier :
    BHistCarrier BoundedRealUpperCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedRealUpperCutToEventFlow
  fromEventFlow := boundedRealUpperCutFromEventFlow

instance boundedRealUpperCutChapterTasteGate :
    ChapterTasteGate BoundedRealUpperCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedRealUpperCutFromEventFlow (boundedRealUpperCutToEventFlow x) = some x
    exact BoundedRealUpperCutTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedRealUpperCutToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BoundedRealUpperCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedRealUpperCutChapterTasteGate

theorem BoundedRealUpperCutTasteGate_single_carrier_alignment :
    (∀ h : BHist, boundedRealUpperCutDecodeBHist (boundedRealUpperCutEncodeBHist h) = h) ∧
      (∀ x : BoundedRealUpperCutUp,
        boundedRealUpperCutFromEventFlow (boundedRealUpperCutToEventFlow x) = some x) ∧
        (∀ x y : BoundedRealUpperCutUp,
          boundedRealUpperCutToEventFlow x = boundedRealUpperCutToEventFlow y → x = y) ∧
          boundedRealUpperCutEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BoundedRealUpperCutTasteGate_single_carrier_alignment_decode,
      BoundedRealUpperCutTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact boundedRealUpperCutToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.BoundedRealUpperCutUp
