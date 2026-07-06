import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProximitySpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProximitySpaceUp : Type where
  | mk (N D S K H C G L : BHist) : ProximitySpaceUp
  deriving DecidableEq

def proximitySpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: proximitySpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: proximitySpaceEncodeBHist h

def proximitySpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (proximitySpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (proximitySpaceDecodeBHist tail)

private theorem proximitySpaceDecode_encode_bhist :
    ∀ h : BHist, proximitySpaceDecodeBHist (proximitySpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def proximitySpaceFields : ProximitySpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProximitySpaceUp.mk N D S K H C G L => [N, D, S, K, H, C, G, L]

def proximitySpaceToEventFlow : ProximitySpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (proximitySpaceFields x).map proximitySpaceEncodeBHist

private def proximitySpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => proximitySpaceEventAtDefault index rest

def proximitySpaceFromEventFlow (ef : EventFlow) : Option ProximitySpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProximitySpaceUp.mk
      (proximitySpaceDecodeBHist (proximitySpaceEventAtDefault 0 ef))
      (proximitySpaceDecodeBHist (proximitySpaceEventAtDefault 1 ef))
      (proximitySpaceDecodeBHist (proximitySpaceEventAtDefault 2 ef))
      (proximitySpaceDecodeBHist (proximitySpaceEventAtDefault 3 ef))
      (proximitySpaceDecodeBHist (proximitySpaceEventAtDefault 4 ef))
      (proximitySpaceDecodeBHist (proximitySpaceEventAtDefault 5 ef))
      (proximitySpaceDecodeBHist (proximitySpaceEventAtDefault 6 ef))
      (proximitySpaceDecodeBHist (proximitySpaceEventAtDefault 7 ef)))

private theorem proximitySpace_round_trip :
    ∀ x : ProximitySpaceUp,
      proximitySpaceFromEventFlow (proximitySpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk N D S K H C G L =>
      change
        some
          (ProximitySpaceUp.mk
            (proximitySpaceDecodeBHist (proximitySpaceEncodeBHist N))
            (proximitySpaceDecodeBHist (proximitySpaceEncodeBHist D))
            (proximitySpaceDecodeBHist (proximitySpaceEncodeBHist S))
            (proximitySpaceDecodeBHist (proximitySpaceEncodeBHist K))
            (proximitySpaceDecodeBHist (proximitySpaceEncodeBHist H))
            (proximitySpaceDecodeBHist (proximitySpaceEncodeBHist C))
            (proximitySpaceDecodeBHist (proximitySpaceEncodeBHist G))
            (proximitySpaceDecodeBHist (proximitySpaceEncodeBHist L))) =
          some (ProximitySpaceUp.mk N D S K H C G L)
      rw [proximitySpaceDecode_encode_bhist N, proximitySpaceDecode_encode_bhist D,
        proximitySpaceDecode_encode_bhist S, proximitySpaceDecode_encode_bhist K,
        proximitySpaceDecode_encode_bhist H, proximitySpaceDecode_encode_bhist C,
        proximitySpaceDecode_encode_bhist G, proximitySpaceDecode_encode_bhist L]

private theorem proximitySpaceToEventFlow_injective {x y : ProximitySpaceUp} :
    proximitySpaceToEventFlow x = proximitySpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      proximitySpaceFromEventFlow (proximitySpaceToEventFlow x) =
        proximitySpaceFromEventFlow (proximitySpaceToEventFlow y) :=
    congrArg proximitySpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (proximitySpace_round_trip x).symm
      (Eq.trans hread (proximitySpace_round_trip y)))

instance proximitySpaceBHistCarrier : BHistCarrier ProximitySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := proximitySpaceToEventFlow
  fromEventFlow := proximitySpaceFromEventFlow

instance proximitySpaceChapterTasteGate :
    ChapterTasteGate ProximitySpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change proximitySpaceFromEventFlow (proximitySpaceToEventFlow x) = some x
    exact proximitySpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (proximitySpaceToEventFlow_injective heq)

theorem ProximitySpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, proximitySpaceDecodeBHist (proximitySpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ProximitySpaceUp) ∧
        Nonempty (ChapterTasteGate ProximitySpaceUp) ∧
          proximitySpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact proximitySpaceDecode_encode_bhist
  · constructor
    · exact ⟨proximitySpaceBHistCarrier⟩
    · constructor
      · exact ⟨proximitySpaceChapterTasteGate⟩
      · rfl

end BEDC.Derived.ProximitySpaceUp
