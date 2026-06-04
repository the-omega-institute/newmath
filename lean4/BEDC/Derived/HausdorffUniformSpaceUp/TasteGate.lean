import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffUniformSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffUniformSpaceUp : Type where
  | mk (U S R A T C P N : BHist) : HausdorffUniformSpaceUp
  deriving DecidableEq

def hausdorffUniformSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffUniformSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffUniformSpaceEncodeBHist h

def hausdorffUniformSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffUniformSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffUniformSpaceDecodeBHist tail)

private theorem HausdorffUniformSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffUniformSpaceFields : HausdorffUniformSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffUniformSpaceUp.mk U S R A T C P N => [U, S, R, A, T, C, P, N]

def hausdorffUniformSpaceToEventFlow : HausdorffUniformSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => hausdorffUniformSpaceFields x |>.map hausdorffUniformSpaceEncodeBHist

private def hausdorffUniformSpaceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => hausdorffUniformSpaceRawAt n rest

def hausdorffUniformSpaceFromEventFlow (flow : EventFlow) : Option HausdorffUniformSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HausdorffUniformSpaceUp.mk
      (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceRawAt 0 flow))
      (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceRawAt 1 flow))
      (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceRawAt 2 flow))
      (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceRawAt 3 flow))
      (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceRawAt 4 flow))
      (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceRawAt 5 flow))
      (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceRawAt 6 flow))
      (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceRawAt 7 flow)))

private theorem HausdorffUniformSpaceTasteGate_single_carrier_alignment_round_trip
    (x : HausdorffUniformSpaceUp) :
    hausdorffUniformSpaceFromEventFlow (hausdorffUniformSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk U S R A T C P N =>
      change
        some
          (HausdorffUniformSpaceUp.mk
            (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceEncodeBHist U))
            (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceEncodeBHist S))
            (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceEncodeBHist R))
            (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceEncodeBHist A))
            (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceEncodeBHist T))
            (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceEncodeBHist C))
            (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceEncodeBHist P))
            (hausdorffUniformSpaceDecodeBHist (hausdorffUniformSpaceEncodeBHist N))) =
          some (HausdorffUniformSpaceUp.mk U S R A T C P N)
      rw [HausdorffUniformSpaceTasteGate_single_carrier_alignment_decode_encode U,
        HausdorffUniformSpaceTasteGate_single_carrier_alignment_decode_encode S,
        HausdorffUniformSpaceTasteGate_single_carrier_alignment_decode_encode R,
        HausdorffUniformSpaceTasteGate_single_carrier_alignment_decode_encode A,
        HausdorffUniformSpaceTasteGate_single_carrier_alignment_decode_encode T,
        HausdorffUniformSpaceTasteGate_single_carrier_alignment_decode_encode C,
        HausdorffUniformSpaceTasteGate_single_carrier_alignment_decode_encode P,
        HausdorffUniformSpaceTasteGate_single_carrier_alignment_decode_encode N]

private theorem HausdorffUniformSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HausdorffUniformSpaceUp} :
    hausdorffUniformSpaceToEventFlow x = hausdorffUniformSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffUniformSpaceFromEventFlow (hausdorffUniformSpaceToEventFlow x) =
        hausdorffUniformSpaceFromEventFlow (hausdorffUniformSpaceToEventFlow y) :=
    congrArg hausdorffUniformSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HausdorffUniformSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HausdorffUniformSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem HausdorffUniformSpaceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : HausdorffUniformSpaceUp,
      hausdorffUniformSpaceFields x = hausdorffUniformSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ S₁ R₁ A₁ T₁ C₁ P₁ N₁ =>
      cases y with
      | mk U₂ S₂ R₂ A₂ T₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance hausdorffUniformSpaceBHistCarrier : BHistCarrier HausdorffUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffUniformSpaceToEventFlow
  fromEventFlow := hausdorffUniformSpaceFromEventFlow

instance hausdorffUniformSpaceChapterTasteGate : ChapterTasteGate HausdorffUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hausdorffUniformSpaceFromEventFlow (hausdorffUniformSpaceToEventFlow x) = some x
    exact HausdorffUniformSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HausdorffUniformSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hausdorffUniformSpaceFieldFaithful : FieldFaithful HausdorffUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hausdorffUniformSpaceFields
  field_faithful := HausdorffUniformSpaceTasteGate_single_carrier_alignment_fields_faithful

instance hausdorffUniformSpaceNontrivial : Nontrivial HausdorffUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HausdorffUniformSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HausdorffUniformSpaceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HausdorffUniformSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hausdorffUniformSpaceChapterTasteGate

namespace TasteGate

theorem HausdorffUniformSpaceTasteGate_single_carrier_alignment :
    ChapterTasteGate HausdorffUniformSpaceUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact hausdorffUniformSpaceChapterTasteGate

end TasteGate

end BEDC.Derived.HausdorffUniformSpaceUp
