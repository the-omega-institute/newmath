import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HemicompactSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HemicompactSpaceUp : Type where
  | mk (M K S F R H C P N : BHist) : HemicompactSpaceUp
  deriving DecidableEq

def hemicompactSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hemicompactSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hemicompactSpaceEncodeBHist h

def hemicompactSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hemicompactSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hemicompactSpaceDecodeBHist tail)

private theorem HemicompactSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hemicompactSpaceDecodeBHist (hemicompactSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hemicompactSpaceFields : HemicompactSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HemicompactSpaceUp.mk M K S F R H C P N => [M, K, S, F, R, H, C, P, N]

def hemicompactSpaceToEventFlow : HemicompactSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hemicompactSpaceFields x).map hemicompactSpaceEncodeBHist

private def hemicompactSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hemicompactSpaceEventAt index rest

def hemicompactSpaceFromEventFlow (ef : EventFlow) : Option HemicompactSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HemicompactSpaceUp.mk
      (hemicompactSpaceDecodeBHist (hemicompactSpaceEventAt 0 ef))
      (hemicompactSpaceDecodeBHist (hemicompactSpaceEventAt 1 ef))
      (hemicompactSpaceDecodeBHist (hemicompactSpaceEventAt 2 ef))
      (hemicompactSpaceDecodeBHist (hemicompactSpaceEventAt 3 ef))
      (hemicompactSpaceDecodeBHist (hemicompactSpaceEventAt 4 ef))
      (hemicompactSpaceDecodeBHist (hemicompactSpaceEventAt 5 ef))
      (hemicompactSpaceDecodeBHist (hemicompactSpaceEventAt 6 ef))
      (hemicompactSpaceDecodeBHist (hemicompactSpaceEventAt 7 ef))
      (hemicompactSpaceDecodeBHist (hemicompactSpaceEventAt 8 ef)))

private theorem HemicompactSpaceTasteGate_single_carrier_alignment_round_trip
    (x : HemicompactSpaceUp) :
    hemicompactSpaceFromEventFlow (hemicompactSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M K S F R H C P N =>
      change
        some
          (HemicompactSpaceUp.mk
            (hemicompactSpaceDecodeBHist (hemicompactSpaceEncodeBHist M))
            (hemicompactSpaceDecodeBHist (hemicompactSpaceEncodeBHist K))
            (hemicompactSpaceDecodeBHist (hemicompactSpaceEncodeBHist S))
            (hemicompactSpaceDecodeBHist (hemicompactSpaceEncodeBHist F))
            (hemicompactSpaceDecodeBHist (hemicompactSpaceEncodeBHist R))
            (hemicompactSpaceDecodeBHist (hemicompactSpaceEncodeBHist H))
            (hemicompactSpaceDecodeBHist (hemicompactSpaceEncodeBHist C))
            (hemicompactSpaceDecodeBHist (hemicompactSpaceEncodeBHist P))
            (hemicompactSpaceDecodeBHist (hemicompactSpaceEncodeBHist N))) =
          some (HemicompactSpaceUp.mk M K S F R H C P N)
      rw [HemicompactSpaceTasteGate_single_carrier_alignment_decode_encode M,
        HemicompactSpaceTasteGate_single_carrier_alignment_decode_encode K,
        HemicompactSpaceTasteGate_single_carrier_alignment_decode_encode S,
        HemicompactSpaceTasteGate_single_carrier_alignment_decode_encode F,
        HemicompactSpaceTasteGate_single_carrier_alignment_decode_encode R,
        HemicompactSpaceTasteGate_single_carrier_alignment_decode_encode H,
        HemicompactSpaceTasteGate_single_carrier_alignment_decode_encode C,
        HemicompactSpaceTasteGate_single_carrier_alignment_decode_encode P,
        HemicompactSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem HemicompactSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HemicompactSpaceUp} :
    hemicompactSpaceToEventFlow x = hemicompactSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hemicompactSpaceFromEventFlow (hemicompactSpaceToEventFlow x) =
        hemicompactSpaceFromEventFlow (hemicompactSpaceToEventFlow y) :=
    congrArg hemicompactSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HemicompactSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HemicompactSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance hemicompactSpaceBHistCarrier : BHistCarrier HemicompactSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hemicompactSpaceToEventFlow
  fromEventFlow := hemicompactSpaceFromEventFlow

instance hemicompactSpaceChapterTasteGate :
    ChapterTasteGate HemicompactSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hemicompactSpaceFromEventFlow (hemicompactSpaceToEventFlow x) = some x
    exact HemicompactSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HemicompactSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate HemicompactSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hemicompactSpaceChapterTasteGate

theorem HemicompactSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, hemicompactSpaceDecodeBHist (hemicompactSpaceEncodeBHist h) = h) ∧
      (∀ x : HemicompactSpaceUp,
        hemicompactSpaceFromEventFlow (hemicompactSpaceToEventFlow x) = some x) ∧
        (∀ x y : HemicompactSpaceUp,
          hemicompactSpaceToEventFlow x = hemicompactSpaceToEventFlow y → x = y) ∧
          hemicompactSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨HemicompactSpaceTasteGate_single_carrier_alignment_decode_encode,
      HemicompactSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HemicompactSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.HemicompactSpaceUp
