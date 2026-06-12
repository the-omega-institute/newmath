import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApproachSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApproachSpaceUp : Type where
  | packet (X D T F H C P N : BHist) : ApproachSpaceUp
  deriving DecidableEq

def approachSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: approachSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: approachSpaceEncodeBHist h

def approachSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (approachSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (approachSpaceDecodeBHist tail)

private theorem ApproachSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, approachSpaceDecodeBHist (approachSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def approachSpaceFields : ApproachSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApproachSpaceUp.packet X D T F H C P N => [X, D, T, F, H, C, P, N]

def approachSpaceToEventFlow : ApproachSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (approachSpaceFields x).map approachSpaceEncodeBHist

private def approachSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => approachSpaceEventAt index rest

def approachSpaceFromEventFlow (ef : EventFlow) : Option ApproachSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ApproachSpaceUp.packet
      (approachSpaceDecodeBHist (approachSpaceEventAt 0 ef))
      (approachSpaceDecodeBHist (approachSpaceEventAt 1 ef))
      (approachSpaceDecodeBHist (approachSpaceEventAt 2 ef))
      (approachSpaceDecodeBHist (approachSpaceEventAt 3 ef))
      (approachSpaceDecodeBHist (approachSpaceEventAt 4 ef))
      (approachSpaceDecodeBHist (approachSpaceEventAt 5 ef))
      (approachSpaceDecodeBHist (approachSpaceEventAt 6 ef))
      (approachSpaceDecodeBHist (approachSpaceEventAt 7 ef)))

private theorem ApproachSpaceTasteGate_single_carrier_alignment_round_trip
    (x : ApproachSpaceUp) :
    approachSpaceFromEventFlow (approachSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | packet X D T F H C P N =>
      change
        some
          (ApproachSpaceUp.packet
            (approachSpaceDecodeBHist (approachSpaceEncodeBHist X))
            (approachSpaceDecodeBHist (approachSpaceEncodeBHist D))
            (approachSpaceDecodeBHist (approachSpaceEncodeBHist T))
            (approachSpaceDecodeBHist (approachSpaceEncodeBHist F))
            (approachSpaceDecodeBHist (approachSpaceEncodeBHist H))
            (approachSpaceDecodeBHist (approachSpaceEncodeBHist C))
            (approachSpaceDecodeBHist (approachSpaceEncodeBHist P))
            (approachSpaceDecodeBHist (approachSpaceEncodeBHist N))) =
          some (ApproachSpaceUp.packet X D T F H C P N)
      rw [ApproachSpaceTasteGate_single_carrier_alignment_decode_encode X,
        ApproachSpaceTasteGate_single_carrier_alignment_decode_encode D,
        ApproachSpaceTasteGate_single_carrier_alignment_decode_encode T,
        ApproachSpaceTasteGate_single_carrier_alignment_decode_encode F,
        ApproachSpaceTasteGate_single_carrier_alignment_decode_encode H,
        ApproachSpaceTasteGate_single_carrier_alignment_decode_encode C,
        ApproachSpaceTasteGate_single_carrier_alignment_decode_encode P,
        ApproachSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem ApproachSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ApproachSpaceUp} :
    approachSpaceToEventFlow x = approachSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      approachSpaceFromEventFlow (approachSpaceToEventFlow x) =
        approachSpaceFromEventFlow (approachSpaceToEventFlow y) :=
    congrArg approachSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ApproachSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ApproachSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance approachSpaceBHistCarrier : BHistCarrier ApproachSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := approachSpaceToEventFlow
  fromEventFlow := approachSpaceFromEventFlow

instance approachSpaceChapterTasteGate : ChapterTasteGate ApproachSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change approachSpaceFromEventFlow (approachSpaceToEventFlow x) = some x
    exact ApproachSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ApproachSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ApproachSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, approachSpaceDecodeBHist (approachSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ApproachSpaceUp) ∧
        Nonempty (ChapterTasteGate ApproachSpaceUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ApproachSpaceTasteGate_single_carrier_alignment_decode_encode,
      ⟨approachSpaceBHistCarrier⟩, ⟨approachSpaceChapterTasteGate⟩⟩

end BEDC.Derived.ApproachSpaceUp
