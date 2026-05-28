import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NormalFamilyUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NormalFamilyUp : Type where
  | mk (F X Y M E I Q H C P L : BHist) : NormalFamilyUp
  deriving DecidableEq

def normalFamilyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: normalFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: normalFamilyEncodeBHist h

def normalFamilyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (normalFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (normalFamilyDecodeBHist tail)

private theorem NormalFamilyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, normalFamilyDecodeBHist (normalFamilyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def normalFamilyFields : NormalFamilyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NormalFamilyUp.mk F X Y M E I Q H C P L => [F, X, Y, M, E, I, Q, H, C, P, L]

def normalFamilyToEventFlow : NormalFamilyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (normalFamilyFields x).map normalFamilyEncodeBHist

private def normalFamilyEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => normalFamilyEventAt index rest

def normalFamilyFromEventFlow (ef : EventFlow) : Option NormalFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NormalFamilyUp.mk
      (normalFamilyDecodeBHist (normalFamilyEventAt 0 ef))
      (normalFamilyDecodeBHist (normalFamilyEventAt 1 ef))
      (normalFamilyDecodeBHist (normalFamilyEventAt 2 ef))
      (normalFamilyDecodeBHist (normalFamilyEventAt 3 ef))
      (normalFamilyDecodeBHist (normalFamilyEventAt 4 ef))
      (normalFamilyDecodeBHist (normalFamilyEventAt 5 ef))
      (normalFamilyDecodeBHist (normalFamilyEventAt 6 ef))
      (normalFamilyDecodeBHist (normalFamilyEventAt 7 ef))
      (normalFamilyDecodeBHist (normalFamilyEventAt 8 ef))
      (normalFamilyDecodeBHist (normalFamilyEventAt 9 ef))
      (normalFamilyDecodeBHist (normalFamilyEventAt 10 ef)))

private theorem NormalFamilyTasteGate_single_carrier_alignment_round_trip
    (x : NormalFamilyUp) :
    normalFamilyFromEventFlow (normalFamilyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F X Y M E I Q H C P L =>
      change
        some
          (NormalFamilyUp.mk
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist F))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist X))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist Y))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist M))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist E))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist I))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist Q))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist H))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist C))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist P))
            (normalFamilyDecodeBHist (normalFamilyEncodeBHist L))) =
          some (NormalFamilyUp.mk F X Y M E I Q H C P L)
      rw [NormalFamilyTasteGate_single_carrier_alignment_decode_encode F,
        NormalFamilyTasteGate_single_carrier_alignment_decode_encode X,
        NormalFamilyTasteGate_single_carrier_alignment_decode_encode Y,
        NormalFamilyTasteGate_single_carrier_alignment_decode_encode M,
        NormalFamilyTasteGate_single_carrier_alignment_decode_encode E,
        NormalFamilyTasteGate_single_carrier_alignment_decode_encode I,
        NormalFamilyTasteGate_single_carrier_alignment_decode_encode Q,
        NormalFamilyTasteGate_single_carrier_alignment_decode_encode H,
        NormalFamilyTasteGate_single_carrier_alignment_decode_encode C,
        NormalFamilyTasteGate_single_carrier_alignment_decode_encode P,
        NormalFamilyTasteGate_single_carrier_alignment_decode_encode L]

private theorem NormalFamilyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NormalFamilyUp} :
    normalFamilyToEventFlow x = normalFamilyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      normalFamilyFromEventFlow (normalFamilyToEventFlow x) =
        normalFamilyFromEventFlow (normalFamilyToEventFlow y) :=
    congrArg normalFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (NormalFamilyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (NormalFamilyTasteGate_single_carrier_alignment_round_trip y)))

private theorem NormalFamilyTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : NormalFamilyUp, normalFamilyFields x = normalFamilyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ X₁ Y₁ M₁ E₁ I₁ Q₁ H₁ C₁ P₁ L₁ =>
      cases y with
      | mk F₂ X₂ Y₂ M₂ E₂ I₂ Q₂ H₂ C₂ P₂ L₂ =>
          cases hfields
          rfl

instance normalFamilyBHistCarrier : BHistCarrier NormalFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := normalFamilyToEventFlow
  fromEventFlow := normalFamilyFromEventFlow

instance normalFamilyChapterTasteGate : ChapterTasteGate NormalFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change normalFamilyFromEventFlow (normalFamilyToEventFlow x) = some x
    exact NormalFamilyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NormalFamilyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance normalFamilyFieldFaithful : FieldFaithful NormalFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := normalFamilyFields
  field_faithful := NormalFamilyTasteGate_single_carrier_alignment_fields_faithful

instance normalFamilyNontrivial : BEDC.Meta.TasteGate.Nontrivial NormalFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NormalFamilyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NormalFamilyUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NormalFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  normalFamilyChapterTasteGate

theorem NormalFamilyTasteGate_single_carrier_alignment :
    (∀ h : BHist, normalFamilyDecodeBHist (normalFamilyEncodeBHist h) = h) ∧
      (∀ x : NormalFamilyUp, normalFamilyFromEventFlow (normalFamilyToEventFlow x) = some x) ∧
        (∀ x y : NormalFamilyUp, normalFamilyToEventFlow x = normalFamilyToEventFlow y →
          x = y) ∧
          normalFamilyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨NormalFamilyTasteGate_single_carrier_alignment_decode_encode,
      NormalFamilyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        NormalFamilyTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.NormalFamilyUp.TasteGate
