import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedRegulatedFunctionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedRegulatedFunctionUp : Type where
  | mk (F B E H C P N : BHist) : BoundedRegulatedFunctionUp
  deriving DecidableEq

def boundedRegulatedFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedRegulatedFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedRegulatedFunctionEncodeBHist h

def boundedRegulatedFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedRegulatedFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedRegulatedFunctionDecodeBHist tail)

private theorem BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedRegulatedFunctionFields : BoundedRegulatedFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedRegulatedFunctionUp.mk F B E H C P N => [F, B, E, H, C, P, N]

def boundedRegulatedFunctionToEventFlow : BoundedRegulatedFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (boundedRegulatedFunctionFields x).map boundedRegulatedFunctionEncodeBHist

private def boundedRegulatedFunctionEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => boundedRegulatedFunctionEventAt index rest

def boundedRegulatedFunctionFromEventFlow
    (ef : EventFlow) : Option BoundedRegulatedFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BoundedRegulatedFunctionUp.mk
      (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAt 0 ef))
      (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAt 1 ef))
      (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAt 2 ef))
      (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAt 3 ef))
      (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAt 4 ef))
      (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAt 5 ef))
      (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEventAt 6 ef)))

private theorem BoundedRegulatedFunctionTasteGate_single_carrier_alignment_round_trip
    (x : BoundedRegulatedFunctionUp) :
    boundedRegulatedFunctionFromEventFlow (boundedRegulatedFunctionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F B E H C P N =>
      change
        some
          (BoundedRegulatedFunctionUp.mk
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist F))
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist B))
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist E))
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist H))
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist C))
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist P))
            (boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist N))) =
          some (BoundedRegulatedFunctionUp.mk F B E H C P N)
      rw [BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode_encode F,
        BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode_encode B,
        BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode_encode E,
        BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode_encode H,
        BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode_encode C,
        BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode_encode P,
        BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode_encode N]

private theorem BoundedRegulatedFunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BoundedRegulatedFunctionUp} :
    boundedRegulatedFunctionToEventFlow x = boundedRegulatedFunctionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedRegulatedFunctionFromEventFlow (boundedRegulatedFunctionToEventFlow x) =
        boundedRegulatedFunctionFromEventFlow (boundedRegulatedFunctionToEventFlow y) :=
    congrArg boundedRegulatedFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BoundedRegulatedFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BoundedRegulatedFunctionTasteGate_single_carrier_alignment_round_trip y)))

instance boundedRegulatedFunctionBHistCarrier :
    BHistCarrier BoundedRegulatedFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedRegulatedFunctionToEventFlow
  fromEventFlow := boundedRegulatedFunctionFromEventFlow

instance boundedRegulatedFunctionChapterTasteGate :
    ChapterTasteGate BoundedRegulatedFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedRegulatedFunctionFromEventFlow (boundedRegulatedFunctionToEventFlow x) =
      some x
    exact BoundedRegulatedFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BoundedRegulatedFunctionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BoundedRegulatedFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      boundedRegulatedFunctionDecodeBHist (boundedRegulatedFunctionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BoundedRegulatedFunctionUp) ∧
        Nonempty (ChapterTasteGate BoundedRegulatedFunctionUp) ∧
          boundedRegulatedFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact BoundedRegulatedFunctionTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact ⟨boundedRegulatedFunctionBHistCarrier⟩
  constructor
  · exact ⟨boundedRegulatedFunctionChapterTasteGate⟩
  · rfl

end BEDC.Derived.BoundedRegulatedFunctionUp.TasteGate
