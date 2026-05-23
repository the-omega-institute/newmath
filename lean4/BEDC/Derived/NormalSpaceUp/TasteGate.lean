import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NormalSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NormalSpaceUp : Type where
  | mk (T F0 F1 D U0 U1 H K P L : BHist) : NormalSpaceUp
  deriving DecidableEq

def normalSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: normalSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: normalSpaceEncodeBHist h

def normalSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (normalSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (normalSpaceDecodeBHist tail)

private theorem NormalSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, normalSpaceDecodeBHist (normalSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def normalSpaceFields : NormalSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NormalSpaceUp.mk T F0 F1 D U0 U1 H K P L => [T, F0, F1, D, U0, U1, H, K, P, L]

def normalSpaceToEventFlow : NormalSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (normalSpaceFields x).map normalSpaceEncodeBHist

private def normalSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => normalSpaceEventAt index rest

def normalSpaceFromEventFlow (ef : EventFlow) : Option NormalSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NormalSpaceUp.mk
      (normalSpaceDecodeBHist (normalSpaceEventAt 0 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 1 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 2 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 3 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 4 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 5 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 6 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 7 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 8 ef))
      (normalSpaceDecodeBHist (normalSpaceEventAt 9 ef)))

private theorem NormalSpaceTasteGate_single_carrier_alignment_round_trip
    (x : NormalSpaceUp) :
    normalSpaceFromEventFlow (normalSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T F0 F1 D U0 U1 H K P L =>
      change
        some
          (NormalSpaceUp.mk
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist T))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist F0))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist F1))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist D))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist U0))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist U1))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist H))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist K))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist P))
            (normalSpaceDecodeBHist (normalSpaceEncodeBHist L))) =
          some (NormalSpaceUp.mk T F0 F1 D U0 U1 H K P L)
      rw [NormalSpaceTasteGate_single_carrier_alignment_decode_encode T,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode F0,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode F1,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode D,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode U0,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode U1,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode H,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode K,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode P,
        NormalSpaceTasteGate_single_carrier_alignment_decode_encode L]

private theorem NormalSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NormalSpaceUp} :
    normalSpaceToEventFlow x = normalSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      normalSpaceFromEventFlow (normalSpaceToEventFlow x) =
        normalSpaceFromEventFlow (normalSpaceToEventFlow y) :=
    congrArg normalSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NormalSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NormalSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance normalSpaceBHistCarrier : BHistCarrier NormalSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := normalSpaceToEventFlow
  fromEventFlow := normalSpaceFromEventFlow

instance normalSpaceChapterTasteGate : ChapterTasteGate NormalSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change normalSpaceFromEventFlow (normalSpaceToEventFlow x) = some x
    exact NormalSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NormalSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem NormalSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, normalSpaceDecodeBHist (normalSpaceEncodeBHist h) = h) ∧
      (∀ x : NormalSpaceUp, normalSpaceFromEventFlow (normalSpaceToEventFlow x) = some x) ∧
        (∀ x y : NormalSpaceUp, normalSpaceToEventFlow x = normalSpaceToEventFlow y → x = y) ∧
          normalSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨NormalSpaceTasteGate_single_carrier_alignment_decode_encode,
      NormalSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => NormalSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.NormalSpaceUp
