import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopIntervalCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopIntervalCoverUp : Type where
  | mk (E D F L W Q R H C P N : BHist) : BishopIntervalCoverUp
  deriving DecidableEq

def bishopIntervalCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopIntervalCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopIntervalCoverEncodeBHist h

def bishopIntervalCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopIntervalCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopIntervalCoverDecodeBHist tail)

private theorem BishopIntervalCoverTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, bishopIntervalCoverDecodeBHist (bishopIntervalCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopIntervalCoverFields : BishopIntervalCoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopIntervalCoverUp.mk E D F L W Q R H C P N => [E, D, F, L, W, Q, R, H, C, P, N]

def bishopIntervalCoverToEventFlow : BishopIntervalCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BishopIntervalCoverUp.mk E D F L W Q R H C P N =>
      (bishopIntervalCoverFields (BishopIntervalCoverUp.mk E D F L W Q R H C P N)).map
        bishopIntervalCoverEncodeBHist

private def bishopIntervalCoverEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopIntervalCoverEventAt index rest

def bishopIntervalCoverFromEventFlow (ef : EventFlow) : Option BishopIntervalCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopIntervalCoverUp.mk
      (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEventAt 0 ef))
      (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEventAt 1 ef))
      (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEventAt 2 ef))
      (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEventAt 3 ef))
      (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEventAt 4 ef))
      (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEventAt 5 ef))
      (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEventAt 6 ef))
      (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEventAt 7 ef))
      (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEventAt 8 ef))
      (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEventAt 9 ef))
      (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEventAt 10 ef)))

private theorem BishopIntervalCoverTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopIntervalCoverUp,
      bishopIntervalCoverFromEventFlow (bishopIntervalCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E D F L W Q R H C P N =>
      change
        some
          (BishopIntervalCoverUp.mk
            (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEncodeBHist E))
            (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEncodeBHist D))
            (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEncodeBHist F))
            (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEncodeBHist L))
            (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEncodeBHist W))
            (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEncodeBHist Q))
            (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEncodeBHist R))
            (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEncodeBHist H))
            (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEncodeBHist C))
            (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEncodeBHist P))
            (bishopIntervalCoverDecodeBHist (bishopIntervalCoverEncodeBHist N))) =
          some (BishopIntervalCoverUp.mk E D F L W Q R H C P N)
      rw [BishopIntervalCoverTasteGate_single_carrier_alignment_decode_encode E,
        BishopIntervalCoverTasteGate_single_carrier_alignment_decode_encode D,
        BishopIntervalCoverTasteGate_single_carrier_alignment_decode_encode F,
        BishopIntervalCoverTasteGate_single_carrier_alignment_decode_encode L,
        BishopIntervalCoverTasteGate_single_carrier_alignment_decode_encode W,
        BishopIntervalCoverTasteGate_single_carrier_alignment_decode_encode Q,
        BishopIntervalCoverTasteGate_single_carrier_alignment_decode_encode R,
        BishopIntervalCoverTasteGate_single_carrier_alignment_decode_encode H,
        BishopIntervalCoverTasteGate_single_carrier_alignment_decode_encode C,
        BishopIntervalCoverTasteGate_single_carrier_alignment_decode_encode P,
        BishopIntervalCoverTasteGate_single_carrier_alignment_decode_encode N]

private theorem BishopIntervalCoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopIntervalCoverUp} :
    bishopIntervalCoverToEventFlow x = bishopIntervalCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopIntervalCoverFromEventFlow (bishopIntervalCoverToEventFlow x) =
        bishopIntervalCoverFromEventFlow (bishopIntervalCoverToEventFlow y) :=
    congrArg bishopIntervalCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopIntervalCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopIntervalCoverTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopIntervalCoverTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : BishopIntervalCoverUp, bishopIntervalCoverFields x = bishopIntervalCoverFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E₁ D₁ F₁ L₁ W₁ Q₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk E₂ D₂ F₂ L₂ W₂ Q₂ R₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance bishopIntervalCoverBHistCarrier : BHistCarrier BishopIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopIntervalCoverToEventFlow
  fromEventFlow := bishopIntervalCoverFromEventFlow

instance bishopIntervalCoverChapterTasteGate : ChapterTasteGate BishopIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopIntervalCoverFromEventFlow (bishopIntervalCoverToEventFlow x) = some x
    exact BishopIntervalCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopIntervalCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance bishopIntervalCoverFieldFaithful : FieldFaithful BishopIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopIntervalCoverFields
  field_faithful := BishopIntervalCoverTasteGate_single_carrier_alignment_fields_faithful

instance bishopIntervalCoverNontrivial : Nontrivial BishopIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopIntervalCoverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopIntervalCoverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BishopIntervalCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopIntervalCoverChapterTasteGate

theorem BishopIntervalCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, bishopIntervalCoverDecodeBHist (bishopIntervalCoverEncodeBHist h) = h) ∧
      (∀ x : BishopIntervalCoverUp,
        bishopIntervalCoverFromEventFlow (bishopIntervalCoverToEventFlow x) = some x) ∧
        (∀ x y : BishopIntervalCoverUp,
          bishopIntervalCoverToEventFlow x = bishopIntervalCoverToEventFlow y → x = y) ∧
          bishopIntervalCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨BishopIntervalCoverTasteGate_single_carrier_alignment_decode_encode,
      BishopIntervalCoverTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => BishopIntervalCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopIntervalCoverUp
