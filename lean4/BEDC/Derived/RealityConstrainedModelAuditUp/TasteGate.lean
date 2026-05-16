import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedModelAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedModelAuditUp : Type where
  | mk : (H Pi O M C T L F S : BHist) → RealityConstrainedModelAuditUp
  deriving DecidableEq

def realityConstrainedModelAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedModelAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedModelAuditEncodeBHist h

def realityConstrainedModelAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedModelAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedModelAuditDecodeBHist tail)

private theorem RealityConstrainedModelAuditTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realityConstrainedModelAuditDecodeBHist
        (realityConstrainedModelAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realityConstrainedModelAuditFields : RealityConstrainedModelAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedModelAuditUp.mk H Pi O M C T L F S => [H, Pi, O, M, C, T, L, F, S]

def realityConstrainedModelAuditToEventFlow : RealityConstrainedModelAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedModelAuditUp.mk H Pi O M C T L F S =>
      [[BMark.b0],
        realityConstrainedModelAuditEncodeBHist H,
        [BMark.b1, BMark.b0],
        realityConstrainedModelAuditEncodeBHist Pi,
        [BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedModelAuditEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedModelAuditEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedModelAuditEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedModelAuditEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realityConstrainedModelAuditEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realityConstrainedModelAuditEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realityConstrainedModelAuditEncodeBHist S]

private def RealityConstrainedModelAuditTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RealityConstrainedModelAuditTasteGate_single_carrier_alignment_eventAtDefault index rest

def realityConstrainedModelAuditFromEventFlow
    (ef : EventFlow) : Option RealityConstrainedModelAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealityConstrainedModelAuditUp.mk
      (realityConstrainedModelAuditDecodeBHist
        (RealityConstrainedModelAuditTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (realityConstrainedModelAuditDecodeBHist
        (RealityConstrainedModelAuditTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (realityConstrainedModelAuditDecodeBHist
        (RealityConstrainedModelAuditTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (realityConstrainedModelAuditDecodeBHist
        (RealityConstrainedModelAuditTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (realityConstrainedModelAuditDecodeBHist
        (RealityConstrainedModelAuditTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (realityConstrainedModelAuditDecodeBHist
        (RealityConstrainedModelAuditTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (realityConstrainedModelAuditDecodeBHist
        (RealityConstrainedModelAuditTasteGate_single_carrier_alignment_eventAtDefault 13 ef))
      (realityConstrainedModelAuditDecodeBHist
        (RealityConstrainedModelAuditTasteGate_single_carrier_alignment_eventAtDefault 15 ef))
      (realityConstrainedModelAuditDecodeBHist
        (RealityConstrainedModelAuditTasteGate_single_carrier_alignment_eventAtDefault 17 ef)))

private theorem RealityConstrainedModelAuditTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealityConstrainedModelAuditUp,
      realityConstrainedModelAuditFromEventFlow
        (realityConstrainedModelAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H Pi O M C T L F S =>
      change
        some
          (RealityConstrainedModelAuditUp.mk
            (realityConstrainedModelAuditDecodeBHist
              (realityConstrainedModelAuditEncodeBHist H))
            (realityConstrainedModelAuditDecodeBHist
              (realityConstrainedModelAuditEncodeBHist Pi))
            (realityConstrainedModelAuditDecodeBHist
              (realityConstrainedModelAuditEncodeBHist O))
            (realityConstrainedModelAuditDecodeBHist
              (realityConstrainedModelAuditEncodeBHist M))
            (realityConstrainedModelAuditDecodeBHist
              (realityConstrainedModelAuditEncodeBHist C))
            (realityConstrainedModelAuditDecodeBHist
              (realityConstrainedModelAuditEncodeBHist T))
            (realityConstrainedModelAuditDecodeBHist
              (realityConstrainedModelAuditEncodeBHist L))
            (realityConstrainedModelAuditDecodeBHist
              (realityConstrainedModelAuditEncodeBHist F))
            (realityConstrainedModelAuditDecodeBHist
              (realityConstrainedModelAuditEncodeBHist S))) =
          some (RealityConstrainedModelAuditUp.mk H Pi O M C T L F S)
      rw [RealityConstrainedModelAuditTasteGate_single_carrier_alignment_decode H,
        RealityConstrainedModelAuditTasteGate_single_carrier_alignment_decode Pi,
        RealityConstrainedModelAuditTasteGate_single_carrier_alignment_decode O,
        RealityConstrainedModelAuditTasteGate_single_carrier_alignment_decode M,
        RealityConstrainedModelAuditTasteGate_single_carrier_alignment_decode C,
        RealityConstrainedModelAuditTasteGate_single_carrier_alignment_decode T,
        RealityConstrainedModelAuditTasteGate_single_carrier_alignment_decode L,
        RealityConstrainedModelAuditTasteGate_single_carrier_alignment_decode F,
        RealityConstrainedModelAuditTasteGate_single_carrier_alignment_decode S]

private theorem RealityConstrainedModelAuditTasteGate_single_carrier_alignment_injective
    {x y : RealityConstrainedModelAuditUp} :
    realityConstrainedModelAuditToEventFlow x =
      realityConstrainedModelAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedModelAuditFromEventFlow (realityConstrainedModelAuditToEventFlow x) =
        realityConstrainedModelAuditFromEventFlow (realityConstrainedModelAuditToEventFlow y) :=
    congrArg realityConstrainedModelAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealityConstrainedModelAuditTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealityConstrainedModelAuditTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealityConstrainedModelAuditTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealityConstrainedModelAuditUp,
      realityConstrainedModelAuditFields x = realityConstrainedModelAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H₁ Pi₁ O₁ M₁ C₁ T₁ L₁ F₁ S₁ =>
      cases y with
      | mk H₂ Pi₂ O₂ M₂ C₂ T₂ L₂ F₂ S₂ =>
          cases hfields
          rfl

instance realityConstrainedModelAuditBHistCarrier :
    BHistCarrier RealityConstrainedModelAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedModelAuditToEventFlow
  fromEventFlow := realityConstrainedModelAuditFromEventFlow

instance realityConstrainedModelAuditChapterTasteGate :
    ChapterTasteGate RealityConstrainedModelAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedModelAuditFromEventFlow
        (realityConstrainedModelAuditToEventFlow x) = some x
    exact RealityConstrainedModelAuditTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealityConstrainedModelAuditTasteGate_single_carrier_alignment_injective heq)

instance realityConstrainedModelAuditFieldFaithful :
    FieldFaithful RealityConstrainedModelAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedModelAuditFields
  field_faithful := RealityConstrainedModelAuditTasteGate_single_carrier_alignment_fields

instance realityConstrainedModelAuditNontrivial : Nontrivial RealityConstrainedModelAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedModelAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedModelAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedModelAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedModelAuditChapterTasteGate

theorem RealityConstrainedModelAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realityConstrainedModelAuditDecodeBHist
        (realityConstrainedModelAuditEncodeBHist h) = h) ∧
      Nonempty (Nontrivial RealityConstrainedModelAuditUp) ∧
        Nonempty (ChapterTasteGate RealityConstrainedModelAuditUp) ∧
          Nonempty (FieldFaithful RealityConstrainedModelAuditUp) ∧
            realityConstrainedModelAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RealityConstrainedModelAuditTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ⟨realityConstrainedModelAuditNontrivial⟩
    · constructor
      · exact ⟨realityConstrainedModelAuditChapterTasteGate⟩
      · constructor
        · exact ⟨realityConstrainedModelAuditFieldFaithful⟩
        · rfl

end BEDC.Derived.RealityConstrainedModelAuditUp
