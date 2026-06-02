import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelianCatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelianCatUp : Type where
  | mk (C H Z B G K Q F : BHist) : AbelianCatUp
  deriving DecidableEq

def abelianCatEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abelianCatEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abelianCatEncodeBHist h

def abelianCatDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abelianCatDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abelianCatDecodeBHist tail)

private theorem AbelianCatTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, abelianCatDecodeBHist (abelianCatEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def abelianCatFields : AbelianCatUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbelianCatUp.mk C H Z B G K Q F => [C, H, Z, B, G, K, Q, F]

def abelianCatToEventFlow : AbelianCatUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (abelianCatFields x).map abelianCatEncodeBHist

private def abelianCatEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => abelianCatEventAtDefault index rest

def abelianCatFromEventFlow (ef : EventFlow) : Option AbelianCatUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AbelianCatUp.mk
      (abelianCatDecodeBHist (abelianCatEventAtDefault 0 ef))
      (abelianCatDecodeBHist (abelianCatEventAtDefault 1 ef))
      (abelianCatDecodeBHist (abelianCatEventAtDefault 2 ef))
      (abelianCatDecodeBHist (abelianCatEventAtDefault 3 ef))
      (abelianCatDecodeBHist (abelianCatEventAtDefault 4 ef))
      (abelianCatDecodeBHist (abelianCatEventAtDefault 5 ef))
      (abelianCatDecodeBHist (abelianCatEventAtDefault 6 ef))
      (abelianCatDecodeBHist (abelianCatEventAtDefault 7 ef)))

private theorem AbelianCatTasteGate_single_carrier_alignment_round_trip
    (x : AbelianCatUp) :
    abelianCatFromEventFlow (abelianCatToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C H Z B G K Q F =>
      change
        some
          (AbelianCatUp.mk
            (abelianCatDecodeBHist (abelianCatEncodeBHist C))
            (abelianCatDecodeBHist (abelianCatEncodeBHist H))
            (abelianCatDecodeBHist (abelianCatEncodeBHist Z))
            (abelianCatDecodeBHist (abelianCatEncodeBHist B))
            (abelianCatDecodeBHist (abelianCatEncodeBHist G))
            (abelianCatDecodeBHist (abelianCatEncodeBHist K))
            (abelianCatDecodeBHist (abelianCatEncodeBHist Q))
            (abelianCatDecodeBHist (abelianCatEncodeBHist F))) =
          some (AbelianCatUp.mk C H Z B G K Q F)
      rw [AbelianCatTasteGate_single_carrier_alignment_decode_encode C,
        AbelianCatTasteGate_single_carrier_alignment_decode_encode H,
        AbelianCatTasteGate_single_carrier_alignment_decode_encode Z,
        AbelianCatTasteGate_single_carrier_alignment_decode_encode B,
        AbelianCatTasteGate_single_carrier_alignment_decode_encode G,
        AbelianCatTasteGate_single_carrier_alignment_decode_encode K,
        AbelianCatTasteGate_single_carrier_alignment_decode_encode Q,
        AbelianCatTasteGate_single_carrier_alignment_decode_encode F]

private theorem AbelianCatTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbelianCatUp} :
    abelianCatToEventFlow x = abelianCatToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      abelianCatFromEventFlow (abelianCatToEventFlow x) =
        abelianCatFromEventFlow (abelianCatToEventFlow y) :=
    congrArg abelianCatFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AbelianCatTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AbelianCatTasteGate_single_carrier_alignment_round_trip y)))

private theorem AbelianCatTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : AbelianCatUp, abelianCatFields x = abelianCatFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C₁ H₁ Z₁ B₁ G₁ K₁ Q₁ F₁ =>
      cases y with
      | mk C₂ H₂ Z₂ B₂ G₂ K₂ Q₂ F₂ =>
          cases hfields
          rfl

instance abelianCatBHistCarrier : BHistCarrier AbelianCatUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abelianCatToEventFlow
  fromEventFlow := abelianCatFromEventFlow

instance abelianCatChapterTasteGate : ChapterTasteGate AbelianCatUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change abelianCatFromEventFlow (abelianCatToEventFlow x) = some x
    exact AbelianCatTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AbelianCatTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance abelianCatFieldFaithful : FieldFaithful AbelianCatUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := abelianCatFields
  field_faithful := AbelianCatTasteGate_single_carrier_alignment_fields_faithful

instance abelianCatNontrivial : Nontrivial AbelianCatUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AbelianCatUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      AbelianCatUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def AbelianCatTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate AbelianCatUp :=
  -- BEDC touchpoint anchor: BHist BMark
  abelianCatChapterTasteGate

theorem AbelianCatTasteGate_single_carrier_alignment :
    (∀ h : BHist, abelianCatDecodeBHist (abelianCatEncodeBHist h) = h) ∧
      (∀ x : AbelianCatUp,
        abelianCatFromEventFlow (abelianCatToEventFlow x) = some x) ∧
        (∀ x y : AbelianCatUp,
          abelianCatToEventFlow x = abelianCatToEventFlow y → x = y) ∧
          (∀ x y : AbelianCatUp, abelianCatFields x = abelianCatFields y → x = y) ∧
            abelianCatEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact AbelianCatTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact AbelianCatTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact AbelianCatTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · constructor
        · exact AbelianCatTasteGate_single_carrier_alignment_fields_faithful
        · rfl

end BEDC.Derived.AbelianCatUp
