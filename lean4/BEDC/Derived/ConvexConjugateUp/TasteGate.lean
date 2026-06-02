import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConvexConjugateUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConvexConjugateUp : Type where
  | mk (F V P D E S H C Q N : BHist) : ConvexConjugateUp
  deriving DecidableEq

def convexConjugateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: convexConjugateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: convexConjugateEncodeBHist h

def convexConjugateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (convexConjugateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (convexConjugateDecodeBHist tail)

private theorem ConvexConjugateTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, convexConjugateDecodeBHist (convexConjugateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def convexConjugateFields : ConvexConjugateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConvexConjugateUp.mk F V P D E S H C Q N => [F, V, P, D, E, S, H, C, Q, N]

def convexConjugateToEventFlow : ConvexConjugateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (convexConjugateFields x).map convexConjugateEncodeBHist

private def convexConjugateEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => convexConjugateEventAt index rest

def convexConjugateFromEventFlow (ef : EventFlow) : Option ConvexConjugateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConvexConjugateUp.mk
      (convexConjugateDecodeBHist (convexConjugateEventAt 0 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAt 1 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAt 2 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAt 3 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAt 4 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAt 5 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAt 6 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAt 7 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAt 8 ef))
      (convexConjugateDecodeBHist (convexConjugateEventAt 9 ef)))

private theorem ConvexConjugateTasteGate_single_carrier_alignment_round_trip
    (x : ConvexConjugateUp) :
    convexConjugateFromEventFlow (convexConjugateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F V P D E S H C Q N =>
      change
        some
          (ConvexConjugateUp.mk
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist F))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist V))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist P))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist D))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist E))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist S))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist H))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist C))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist Q))
            (convexConjugateDecodeBHist (convexConjugateEncodeBHist N))) =
          some (ConvexConjugateUp.mk F V P D E S H C Q N)
      rw [ConvexConjugateTasteGate_single_carrier_alignment_decode_encode F,
        ConvexConjugateTasteGate_single_carrier_alignment_decode_encode V,
        ConvexConjugateTasteGate_single_carrier_alignment_decode_encode P,
        ConvexConjugateTasteGate_single_carrier_alignment_decode_encode D,
        ConvexConjugateTasteGate_single_carrier_alignment_decode_encode E,
        ConvexConjugateTasteGate_single_carrier_alignment_decode_encode S,
        ConvexConjugateTasteGate_single_carrier_alignment_decode_encode H,
        ConvexConjugateTasteGate_single_carrier_alignment_decode_encode C,
        ConvexConjugateTasteGate_single_carrier_alignment_decode_encode Q,
        ConvexConjugateTasteGate_single_carrier_alignment_decode_encode N]

private theorem ConvexConjugateTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConvexConjugateUp} :
    convexConjugateToEventFlow x = convexConjugateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      convexConjugateFromEventFlow (convexConjugateToEventFlow x) =
        convexConjugateFromEventFlow (convexConjugateToEventFlow y) :=
    congrArg convexConjugateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ConvexConjugateTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConvexConjugateTasteGate_single_carrier_alignment_round_trip y)))

instance convexConjugateBHistCarrier : BHistCarrier ConvexConjugateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := convexConjugateToEventFlow
  fromEventFlow := convexConjugateFromEventFlow

instance convexConjugateChapterTasteGate : ChapterTasteGate ConvexConjugateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change convexConjugateFromEventFlow (convexConjugateToEventFlow x) = some x
    exact ConvexConjugateTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConvexConjugateTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ConvexConjugateTasteGate_single_carrier_alignment :
    convexConjugateDecodeBHist (convexConjugateEncodeBHist BHist.Empty) = BHist.Empty ∧
      (forall x : ConvexConjugateUp,
        convexConjugateFromEventFlow (convexConjugateToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · exact ConvexConjugateTasteGate_single_carrier_alignment_round_trip

end TasteGate
end BEDC.Derived.ConvexConjugateUp
