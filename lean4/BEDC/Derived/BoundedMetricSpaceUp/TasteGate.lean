import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedMetricSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedMetricSpaceUp : Type where
  | mk (X B D R H C P N : BHist) : BoundedMetricSpaceUp
  deriving DecidableEq

def boundedMetricSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedMetricSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedMetricSpaceEncodeBHist h

def boundedMetricSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedMetricSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedMetricSpaceDecodeBHist tail)

private theorem boundedMetricSpaceDecodeEncode :
    ∀ h : BHist, boundedMetricSpaceDecodeBHist (boundedMetricSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedMetricSpaceFields : BoundedMetricSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedMetricSpaceUp.mk X B D R H C P N => [X, B, D, R, H, C, P, N]

def boundedMetricSpaceToEventFlow : BoundedMetricSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedMetricSpaceFields x).map boundedMetricSpaceEncodeBHist

private def boundedMetricSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedMetricSpaceEventAtDefault index rest

def boundedMetricSpaceFromEventFlow : EventFlow → Option BoundedMetricSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BoundedMetricSpaceUp.mk
        (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEventAtDefault 0 ef))
        (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEventAtDefault 1 ef))
        (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEventAtDefault 2 ef))
        (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEventAtDefault 3 ef))
        (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEventAtDefault 4 ef))
        (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEventAtDefault 5 ef))
        (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEventAtDefault 6 ef))
        (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEventAtDefault 7 ef)))

private theorem boundedMetricSpaceRoundTrip :
    ∀ x : BoundedMetricSpaceUp,
      boundedMetricSpaceFromEventFlow (boundedMetricSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X B D R H C P N =>
      change
        some
          (BoundedMetricSpaceUp.mk
            (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEncodeBHist X))
            (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEncodeBHist B))
            (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEncodeBHist D))
            (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEncodeBHist R))
            (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEncodeBHist H))
            (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEncodeBHist C))
            (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEncodeBHist P))
            (boundedMetricSpaceDecodeBHist (boundedMetricSpaceEncodeBHist N))) =
          some (BoundedMetricSpaceUp.mk X B D R H C P N)
      rw [boundedMetricSpaceDecodeEncode X, boundedMetricSpaceDecodeEncode B,
        boundedMetricSpaceDecodeEncode D, boundedMetricSpaceDecodeEncode R,
        boundedMetricSpaceDecodeEncode H, boundedMetricSpaceDecodeEncode C,
        boundedMetricSpaceDecodeEncode P, boundedMetricSpaceDecodeEncode N]

private theorem boundedMetricSpaceToEventFlow_injective
    {x y : BoundedMetricSpaceUp} :
    boundedMetricSpaceToEventFlow x = boundedMetricSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedMetricSpaceFromEventFlow (boundedMetricSpaceToEventFlow x) =
        boundedMetricSpaceFromEventFlow (boundedMetricSpaceToEventFlow y) :=
    congrArg boundedMetricSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundedMetricSpaceRoundTrip x).symm
      (Eq.trans hread (boundedMetricSpaceRoundTrip y)))

instance boundedMetricSpaceBHistCarrier : BHistCarrier BoundedMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedMetricSpaceToEventFlow
  fromEventFlow := boundedMetricSpaceFromEventFlow

instance boundedMetricSpaceChapterTasteGate : ChapterTasteGate BoundedMetricSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedMetricSpaceFromEventFlow (boundedMetricSpaceToEventFlow x) = some x
    exact boundedMetricSpaceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedMetricSpaceToEventFlow_injective heq)

theorem BoundedMetricSpaceTasteGate_single_carrier_alignment :
    boundedMetricSpaceEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ h : BHist, boundedMetricSpaceDecodeBHist (boundedMetricSpaceEncodeBHist h) = h) ∧
        (∀ x : BoundedMetricSpaceUp,
          boundedMetricSpaceFromEventFlow (boundedMetricSpaceToEventFlow x) = some x) ∧
          Nonempty (BHistCarrier BoundedMetricSpaceUp) ∧
            Nonempty (ChapterTasteGate BoundedMetricSpaceUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl, boundedMetricSpaceDecodeEncode, boundedMetricSpaceRoundTrip,
      ⟨boundedMetricSpaceBHistCarrier⟩, ⟨boundedMetricSpaceChapterTasteGate⟩⟩

end BEDC.Derived.BoundedMetricSpaceUp
