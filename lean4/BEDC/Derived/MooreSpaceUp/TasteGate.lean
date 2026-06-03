import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MooreSpaceUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MooreSpaceUp : Type where
  | mk (T N D S H C P L : BHist) : MooreSpaceUp
  deriving DecidableEq

def mooreSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mooreSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mooreSpaceEncodeBHist h

def mooreSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mooreSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mooreSpaceDecodeBHist tail)

private theorem MooreSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, mooreSpaceDecodeBHist (mooreSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mooreSpaceFields : MooreSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MooreSpaceUp.mk T N D S H C P L => [T, N, D, S, H, C, P, L]

def mooreSpaceToEventFlow : MooreSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (mooreSpaceFields x).map mooreSpaceEncodeBHist

private def mooreSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => mooreSpaceEventAt index rest

def mooreSpaceFromEventFlow (ef : EventFlow) : Option MooreSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MooreSpaceUp.mk
      (mooreSpaceDecodeBHist (mooreSpaceEventAt 0 ef))
      (mooreSpaceDecodeBHist (mooreSpaceEventAt 1 ef))
      (mooreSpaceDecodeBHist (mooreSpaceEventAt 2 ef))
      (mooreSpaceDecodeBHist (mooreSpaceEventAt 3 ef))
      (mooreSpaceDecodeBHist (mooreSpaceEventAt 4 ef))
      (mooreSpaceDecodeBHist (mooreSpaceEventAt 5 ef))
      (mooreSpaceDecodeBHist (mooreSpaceEventAt 6 ef))
      (mooreSpaceDecodeBHist (mooreSpaceEventAt 7 ef)))

private theorem MooreSpaceTasteGate_single_carrier_alignment_round_trip
    (x : MooreSpaceUp) :
    mooreSpaceFromEventFlow (mooreSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T N D S H C P L =>
      change
        some
          (MooreSpaceUp.mk
            (mooreSpaceDecodeBHist (mooreSpaceEncodeBHist T))
            (mooreSpaceDecodeBHist (mooreSpaceEncodeBHist N))
            (mooreSpaceDecodeBHist (mooreSpaceEncodeBHist D))
            (mooreSpaceDecodeBHist (mooreSpaceEncodeBHist S))
            (mooreSpaceDecodeBHist (mooreSpaceEncodeBHist H))
            (mooreSpaceDecodeBHist (mooreSpaceEncodeBHist C))
            (mooreSpaceDecodeBHist (mooreSpaceEncodeBHist P))
            (mooreSpaceDecodeBHist (mooreSpaceEncodeBHist L))) =
          some (MooreSpaceUp.mk T N D S H C P L)
      rw [MooreSpaceTasteGate_single_carrier_alignment_decode_encode T,
        MooreSpaceTasteGate_single_carrier_alignment_decode_encode N,
        MooreSpaceTasteGate_single_carrier_alignment_decode_encode D,
        MooreSpaceTasteGate_single_carrier_alignment_decode_encode S,
        MooreSpaceTasteGate_single_carrier_alignment_decode_encode H,
        MooreSpaceTasteGate_single_carrier_alignment_decode_encode C,
        MooreSpaceTasteGate_single_carrier_alignment_decode_encode P,
        MooreSpaceTasteGate_single_carrier_alignment_decode_encode L]

private theorem MooreSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MooreSpaceUp} :
    mooreSpaceToEventFlow x = mooreSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mooreSpaceFromEventFlow (mooreSpaceToEventFlow x) =
        mooreSpaceFromEventFlow (mooreSpaceToEventFlow y) :=
    congrArg mooreSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MooreSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MooreSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance mooreSpaceBHistCarrier : BHistCarrier MooreSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mooreSpaceToEventFlow
  fromEventFlow := mooreSpaceFromEventFlow

instance mooreSpaceChapterTasteGate : ChapterTasteGate MooreSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mooreSpaceFromEventFlow (mooreSpaceToEventFlow x) = some x
    exact MooreSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MooreSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem MooreSpaceTasteGate_single_carrier_alignment :
    mooreSpaceDecodeBHist (mooreSpaceEncodeBHist BHist.Empty) = BHist.Empty ∧
      (forall x : MooreSpaceUp, mooreSpaceFromEventFlow (mooreSpaceToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · exact MooreSpaceTasteGate_single_carrier_alignment_round_trip

end TasteGate
end BEDC.Derived.MooreSpaceUp
