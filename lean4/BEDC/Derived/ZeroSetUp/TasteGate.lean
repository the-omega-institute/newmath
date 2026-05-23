import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ZeroSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ZeroSetUp : Type where
  | mk (F R E T S H C P N : BHist) : ZeroSetUp
  deriving DecidableEq

def zeroSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: zeroSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: zeroSetEncodeBHist h

def zeroSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (zeroSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (zeroSetDecodeBHist tail)

private theorem ZeroSetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, zeroSetDecodeBHist (zeroSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def zeroSetFields : ZeroSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ZeroSetUp.mk F R E T S H C P N => [F, R, E, T, S, H, C, P, N]

def zeroSetToEventFlow : ZeroSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (zeroSetFields x).map zeroSetEncodeBHist

private def zeroSetEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => zeroSetEventAt index rest

def zeroSetFromEventFlow (ef : EventFlow) : Option ZeroSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ZeroSetUp.mk
      (zeroSetDecodeBHist (zeroSetEventAt 0 ef))
      (zeroSetDecodeBHist (zeroSetEventAt 1 ef))
      (zeroSetDecodeBHist (zeroSetEventAt 2 ef))
      (zeroSetDecodeBHist (zeroSetEventAt 3 ef))
      (zeroSetDecodeBHist (zeroSetEventAt 4 ef))
      (zeroSetDecodeBHist (zeroSetEventAt 5 ef))
      (zeroSetDecodeBHist (zeroSetEventAt 6 ef))
      (zeroSetDecodeBHist (zeroSetEventAt 7 ef))
      (zeroSetDecodeBHist (zeroSetEventAt 8 ef)))

private theorem ZeroSetTasteGate_single_carrier_alignment_round_trip
    (x : ZeroSetUp) :
    zeroSetFromEventFlow (zeroSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F R E T S H C P N =>
      change
        some
          (ZeroSetUp.mk
            (zeroSetDecodeBHist (zeroSetEncodeBHist F))
            (zeroSetDecodeBHist (zeroSetEncodeBHist R))
            (zeroSetDecodeBHist (zeroSetEncodeBHist E))
            (zeroSetDecodeBHist (zeroSetEncodeBHist T))
            (zeroSetDecodeBHist (zeroSetEncodeBHist S))
            (zeroSetDecodeBHist (zeroSetEncodeBHist H))
            (zeroSetDecodeBHist (zeroSetEncodeBHist C))
            (zeroSetDecodeBHist (zeroSetEncodeBHist P))
            (zeroSetDecodeBHist (zeroSetEncodeBHist N))) =
          some (ZeroSetUp.mk F R E T S H C P N)
      rw [ZeroSetTasteGate_single_carrier_alignment_decode_encode F,
        ZeroSetTasteGate_single_carrier_alignment_decode_encode R,
        ZeroSetTasteGate_single_carrier_alignment_decode_encode E,
        ZeroSetTasteGate_single_carrier_alignment_decode_encode T,
        ZeroSetTasteGate_single_carrier_alignment_decode_encode S,
        ZeroSetTasteGate_single_carrier_alignment_decode_encode H,
        ZeroSetTasteGate_single_carrier_alignment_decode_encode C,
        ZeroSetTasteGate_single_carrier_alignment_decode_encode P,
        ZeroSetTasteGate_single_carrier_alignment_decode_encode N]

private theorem ZeroSetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ZeroSetUp} :
    zeroSetToEventFlow x = zeroSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      zeroSetFromEventFlow (zeroSetToEventFlow x) =
        zeroSetFromEventFlow (zeroSetToEventFlow y) :=
    congrArg zeroSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ZeroSetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ZeroSetTasteGate_single_carrier_alignment_round_trip y)))

private theorem ZeroSetTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ZeroSetUp, zeroSetFields x = zeroSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ R₁ E₁ T₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ R₂ E₂ T₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance zeroSetBHistCarrier : BHistCarrier ZeroSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := zeroSetToEventFlow
  fromEventFlow := zeroSetFromEventFlow

instance zeroSetChapterTasteGate : ChapterTasteGate ZeroSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change zeroSetFromEventFlow (zeroSetToEventFlow x) = some x
    exact ZeroSetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ZeroSetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance zeroSetFieldFaithful : FieldFaithful ZeroSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := zeroSetFields
  field_faithful := ZeroSetTasteGate_single_carrier_alignment_fields_faithful

instance zeroSetNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ZeroSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ZeroSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ZeroSetUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def ZeroSetTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ZeroSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  zeroSetChapterTasteGate

theorem ZeroSetTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ZeroSetUp) ∧
      Nonempty (FieldFaithful ZeroSetUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial ZeroSetUp) ∧
      (∀ h : BHist, zeroSetDecodeBHist (zeroSetEncodeBHist h) = h) ∧
      (∀ x : ZeroSetUp, zeroSetFromEventFlow (zeroSetToEventFlow x) = some x) ∧
      (∀ x y : ZeroSetUp, zeroSetToEventFlow x = zeroSetToEventFlow y → x = y) ∧
      zeroSetEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨zeroSetChapterTasteGate⟩,
      ⟨zeroSetFieldFaithful⟩,
      ⟨zeroSetNontrivial⟩,
      ZeroSetTasteGate_single_carrier_alignment_decode_encode,
      ZeroSetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => ZeroSetTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ZeroSetUp
