import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegulatedPrimitiveUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegulatedPrimitiveUp : Type where
  | mk (I G W D R E H C P N : BHist) : RegulatedPrimitiveUp
  deriving DecidableEq

def regulatedPrimitiveEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regulatedPrimitiveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regulatedPrimitiveEncodeBHist h

def regulatedPrimitiveDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regulatedPrimitiveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regulatedPrimitiveDecodeBHist tail)

private theorem RegulatedPrimitiveTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regulatedPrimitiveDecodeBHist
        (regulatedPrimitiveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regulatedPrimitiveFields :
    RegulatedPrimitiveUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegulatedPrimitiveUp.mk I G W D R E H C P N => [I, G, W, D, R, E, H, C, P, N]

def regulatedPrimitiveToEventFlow :
    RegulatedPrimitiveUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regulatedPrimitiveFields x).map regulatedPrimitiveEncodeBHist

private def regulatedPrimitiveEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regulatedPrimitiveEventAtDefault index rest

def regulatedPrimitiveFromEventFlow
    (ef : EventFlow) : Option RegulatedPrimitiveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegulatedPrimitiveUp.mk
      (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEventAtDefault 0 ef))
      (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEventAtDefault 1 ef))
      (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEventAtDefault 2 ef))
      (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEventAtDefault 3 ef))
      (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEventAtDefault 4 ef))
      (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEventAtDefault 5 ef))
      (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEventAtDefault 6 ef))
      (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEventAtDefault 7 ef))
      (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEventAtDefault 8 ef))
      (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEventAtDefault 9 ef)))

private theorem RegulatedPrimitiveTasteGate_single_carrier_alignment_round_trip
    (x : RegulatedPrimitiveUp) :
    regulatedPrimitiveFromEventFlow
      (regulatedPrimitiveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I G W D R E H C P N =>
      change
        some
          (RegulatedPrimitiveUp.mk
            (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEncodeBHist I))
            (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEncodeBHist G))
            (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEncodeBHist W))
            (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEncodeBHist D))
            (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEncodeBHist R))
            (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEncodeBHist E))
            (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEncodeBHist H))
            (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEncodeBHist C))
            (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEncodeBHist P))
            (regulatedPrimitiveDecodeBHist (regulatedPrimitiveEncodeBHist N))) =
          some (RegulatedPrimitiveUp.mk I G W D R E H C P N)
      rw [RegulatedPrimitiveTasteGate_single_carrier_alignment_decode I,
        RegulatedPrimitiveTasteGate_single_carrier_alignment_decode G,
        RegulatedPrimitiveTasteGate_single_carrier_alignment_decode W,
        RegulatedPrimitiveTasteGate_single_carrier_alignment_decode D,
        RegulatedPrimitiveTasteGate_single_carrier_alignment_decode R,
        RegulatedPrimitiveTasteGate_single_carrier_alignment_decode E,
        RegulatedPrimitiveTasteGate_single_carrier_alignment_decode H,
        RegulatedPrimitiveTasteGate_single_carrier_alignment_decode C,
        RegulatedPrimitiveTasteGate_single_carrier_alignment_decode P,
        RegulatedPrimitiveTasteGate_single_carrier_alignment_decode N]

private theorem RegulatedPrimitiveTasteGate_single_carrier_alignment_injective
    {x y : RegulatedPrimitiveUp} :
    regulatedPrimitiveToEventFlow x =
      regulatedPrimitiveToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regulatedPrimitiveFromEventFlow
          (regulatedPrimitiveToEventFlow x) =
        regulatedPrimitiveFromEventFlow
          (regulatedPrimitiveToEventFlow y) :=
    congrArg regulatedPrimitiveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegulatedPrimitiveTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegulatedPrimitiveTasteGate_single_carrier_alignment_round_trip y)))

instance regulatedPrimitiveBHistCarrier :
    BHistCarrier RegulatedPrimitiveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regulatedPrimitiveToEventFlow
  fromEventFlow := regulatedPrimitiveFromEventFlow

instance regulatedPrimitiveChapterTasteGate :
    ChapterTasteGate RegulatedPrimitiveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regulatedPrimitiveFromEventFlow
        (regulatedPrimitiveToEventFlow x) = some x
    exact RegulatedPrimitiveTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegulatedPrimitiveTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate RegulatedPrimitiveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regulatedPrimitiveChapterTasteGate

theorem RegulatedPrimitiveTasteGate_single_carrier_alignment :
    (∀ h : BHist, regulatedPrimitiveDecodeBHist (regulatedPrimitiveEncodeBHist h) = h) ∧
      (∀ x : RegulatedPrimitiveUp,
        regulatedPrimitiveFromEventFlow (regulatedPrimitiveToEventFlow x) = some x) ∧
        (∀ x y : RegulatedPrimitiveUp,
          regulatedPrimitiveToEventFlow x = regulatedPrimitiveToEventFlow y → x = y) ∧
          regulatedPrimitiveEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegulatedPrimitiveTasteGate_single_carrier_alignment_decode
  · constructor
    · exact RegulatedPrimitiveTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact RegulatedPrimitiveTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.RegulatedPrimitiveUp
