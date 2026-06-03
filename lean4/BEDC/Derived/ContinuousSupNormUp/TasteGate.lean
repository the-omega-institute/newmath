import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuousSupNormUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuousSupNormUp : Type where
  | mk (K F R O M B H C P N : BHist) : ContinuousSupNormUp
  deriving DecidableEq

def continuousSupNormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuousSupNormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuousSupNormEncodeBHist h

def continuousSupNormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuousSupNormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuousSupNormDecodeBHist tail)

private theorem ContinuousSupNormTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, continuousSupNormDecodeBHist (continuousSupNormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def continuousSupNormFields : ContinuousSupNormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuousSupNormUp.mk K F R O M B H C P N => [K, F, R, O, M, B, H, C, P, N]

def continuousSupNormToEventFlow : ContinuousSupNormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (continuousSupNormFields x).map continuousSupNormEncodeBHist

private def continuousSupNormEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => continuousSupNormEventAt index rest

def continuousSupNormFromEventFlow (ef : EventFlow) : Option ContinuousSupNormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContinuousSupNormUp.mk
      (continuousSupNormDecodeBHist (continuousSupNormEventAt 0 ef))
      (continuousSupNormDecodeBHist (continuousSupNormEventAt 1 ef))
      (continuousSupNormDecodeBHist (continuousSupNormEventAt 2 ef))
      (continuousSupNormDecodeBHist (continuousSupNormEventAt 3 ef))
      (continuousSupNormDecodeBHist (continuousSupNormEventAt 4 ef))
      (continuousSupNormDecodeBHist (continuousSupNormEventAt 5 ef))
      (continuousSupNormDecodeBHist (continuousSupNormEventAt 6 ef))
      (continuousSupNormDecodeBHist (continuousSupNormEventAt 7 ef))
      (continuousSupNormDecodeBHist (continuousSupNormEventAt 8 ef))
      (continuousSupNormDecodeBHist (continuousSupNormEventAt 9 ef)))

private theorem ContinuousSupNormTasteGate_single_carrier_alignment_round_trip
    (x : ContinuousSupNormUp) :
    continuousSupNormFromEventFlow (continuousSupNormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F R O M B H C P N =>
      change
        some
          (ContinuousSupNormUp.mk
            (continuousSupNormDecodeBHist (continuousSupNormEncodeBHist K))
            (continuousSupNormDecodeBHist (continuousSupNormEncodeBHist F))
            (continuousSupNormDecodeBHist (continuousSupNormEncodeBHist R))
            (continuousSupNormDecodeBHist (continuousSupNormEncodeBHist O))
            (continuousSupNormDecodeBHist (continuousSupNormEncodeBHist M))
            (continuousSupNormDecodeBHist (continuousSupNormEncodeBHist B))
            (continuousSupNormDecodeBHist (continuousSupNormEncodeBHist H))
            (continuousSupNormDecodeBHist (continuousSupNormEncodeBHist C))
            (continuousSupNormDecodeBHist (continuousSupNormEncodeBHist P))
            (continuousSupNormDecodeBHist (continuousSupNormEncodeBHist N))) =
          some (ContinuousSupNormUp.mk K F R O M B H C P N)
      rw [ContinuousSupNormTasteGate_single_carrier_alignment_decode_encode K,
        ContinuousSupNormTasteGate_single_carrier_alignment_decode_encode F,
        ContinuousSupNormTasteGate_single_carrier_alignment_decode_encode R,
        ContinuousSupNormTasteGate_single_carrier_alignment_decode_encode O,
        ContinuousSupNormTasteGate_single_carrier_alignment_decode_encode M,
        ContinuousSupNormTasteGate_single_carrier_alignment_decode_encode B,
        ContinuousSupNormTasteGate_single_carrier_alignment_decode_encode H,
        ContinuousSupNormTasteGate_single_carrier_alignment_decode_encode C,
        ContinuousSupNormTasteGate_single_carrier_alignment_decode_encode P,
        ContinuousSupNormTasteGate_single_carrier_alignment_decode_encode N]

private theorem ContinuousSupNormTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContinuousSupNormUp} :
    continuousSupNormToEventFlow x = continuousSupNormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuousSupNormFromEventFlow (continuousSupNormToEventFlow x) =
        continuousSupNormFromEventFlow (continuousSupNormToEventFlow y) :=
    congrArg continuousSupNormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ContinuousSupNormTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ContinuousSupNormTasteGate_single_carrier_alignment_round_trip y)))

private theorem ContinuousSupNormTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : ContinuousSupNormUp, continuousSupNormFields x = continuousSupNormFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ F₁ R₁ O₁ M₁ B₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ F₂ R₂ O₂ M₂ B₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance continuousSupNormBHistCarrier : BHistCarrier ContinuousSupNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuousSupNormToEventFlow
  fromEventFlow := continuousSupNormFromEventFlow

instance continuousSupNormChapterTasteGate : ChapterTasteGate ContinuousSupNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change continuousSupNormFromEventFlow (continuousSupNormToEventFlow x) = some x
    exact ContinuousSupNormTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ContinuousSupNormTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance continuousSupNormFieldFaithful : FieldFaithful ContinuousSupNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := continuousSupNormFields
  field_faithful := ContinuousSupNormTasteGate_single_carrier_alignment_fields_faithful

instance continuousSupNormNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ContinuousSupNormUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ContinuousSupNormUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ContinuousSupNormUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def ContinuousSupNormTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate ContinuousSupNormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  continuousSupNormChapterTasteGate

theorem ContinuousSupNormTasteGate_single_carrier_alignment :
    (∀ h : BHist, continuousSupNormDecodeBHist (continuousSupNormEncodeBHist h) = h) ∧
      (∀ x : ContinuousSupNormUp,
        continuousSupNormFromEventFlow (continuousSupNormToEventFlow x) = some x) ∧
        (∀ x y : ContinuousSupNormUp,
          continuousSupNormToEventFlow x = continuousSupNormToEventFlow y → x = y) ∧
          continuousSupNormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨ContinuousSupNormTasteGate_single_carrier_alignment_decode_encode,
      ContinuousSupNormTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => ContinuousSupNormTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ContinuousSupNormUp.TasteGate

namespace BEDC.Derived.ContinuousSupNormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

theorem ContinuousSupNormTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      TasteGate.continuousSupNormDecodeBHist (TasteGate.continuousSupNormEncodeBHist h) =
        h) ∧
      (∀ x : TasteGate.ContinuousSupNormUp,
        TasteGate.continuousSupNormFromEventFlow (TasteGate.continuousSupNormToEventFlow x) =
          some x) ∧
        (∀ x y : TasteGate.ContinuousSupNormUp,
          TasteGate.continuousSupNormToEventFlow x =
              TasteGate.continuousSupNormToEventFlow y →
            x = y) ∧
          TasteGate.continuousSupNormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact TasteGate.ContinuousSupNormTasteGate_single_carrier_alignment

end BEDC.Derived.ContinuousSupNormUp
