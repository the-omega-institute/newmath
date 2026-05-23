import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorSetUp : Type where
  | mk (T G I D R E : BHist) : CantorSetUp
  deriving DecidableEq

def CantorSetTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1]

def CantorSetTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CantorSetTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CantorSetTasteGate_single_carrier_alignment_encodeBHist h

def CantorSetTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (CantorSetTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (CantorSetTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CantorSetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CantorSetTasteGate_single_carrier_alignment_decodeBHist
          (CantorSetTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CantorSetTasteGate_single_carrier_alignment_fields : CantorSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorSetUp.mk T G I D R E => [T, G, I, D, R, E]

def CantorSetTasteGate_single_carrier_alignment_toEventFlow : CantorSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CantorSetUp.mk T G I D R E =>
      [CantorSetTasteGate_single_carrier_alignment_tag,
        CantorSetTasteGate_single_carrier_alignment_encodeBHist T,
        CantorSetTasteGate_single_carrier_alignment_encodeBHist G,
        CantorSetTasteGate_single_carrier_alignment_encodeBHist I,
        CantorSetTasteGate_single_carrier_alignment_encodeBHist D,
        CantorSetTasteGate_single_carrier_alignment_encodeBHist R,
        CantorSetTasteGate_single_carrier_alignment_encodeBHist E]

private def CantorSetTasteGate_single_carrier_alignment_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => CantorSetTasteGate_single_carrier_alignment_eventAt index rest

def CantorSetTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CantorSetUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CantorSetUp.mk
          (CantorSetTasteGate_single_carrier_alignment_decodeBHist
            (CantorSetTasteGate_single_carrier_alignment_eventAt 1 ef))
          (CantorSetTasteGate_single_carrier_alignment_decodeBHist
            (CantorSetTasteGate_single_carrier_alignment_eventAt 2 ef))
          (CantorSetTasteGate_single_carrier_alignment_decodeBHist
            (CantorSetTasteGate_single_carrier_alignment_eventAt 3 ef))
          (CantorSetTasteGate_single_carrier_alignment_decodeBHist
            (CantorSetTasteGate_single_carrier_alignment_eventAt 4 ef))
          (CantorSetTasteGate_single_carrier_alignment_decodeBHist
            (CantorSetTasteGate_single_carrier_alignment_eventAt 5 ef))
          (CantorSetTasteGate_single_carrier_alignment_decodeBHist
            (CantorSetTasteGate_single_carrier_alignment_eventAt 6 ef)))

private theorem CantorSetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CantorSetUp,
      CantorSetTasteGate_single_carrier_alignment_fromEventFlow
          (CantorSetTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T G I D R E =>
      change
        some
          (CantorSetUp.mk
            (CantorSetTasteGate_single_carrier_alignment_decodeBHist
              (CantorSetTasteGate_single_carrier_alignment_encodeBHist T))
            (CantorSetTasteGate_single_carrier_alignment_decodeBHist
              (CantorSetTasteGate_single_carrier_alignment_encodeBHist G))
            (CantorSetTasteGate_single_carrier_alignment_decodeBHist
              (CantorSetTasteGate_single_carrier_alignment_encodeBHist I))
            (CantorSetTasteGate_single_carrier_alignment_decodeBHist
              (CantorSetTasteGate_single_carrier_alignment_encodeBHist D))
            (CantorSetTasteGate_single_carrier_alignment_decodeBHist
              (CantorSetTasteGate_single_carrier_alignment_encodeBHist R))
            (CantorSetTasteGate_single_carrier_alignment_decodeBHist
              (CantorSetTasteGate_single_carrier_alignment_encodeBHist E))) =
          some (CantorSetUp.mk T G I D R E)
      rw [CantorSetTasteGate_single_carrier_alignment_decode_encode T,
        CantorSetTasteGate_single_carrier_alignment_decode_encode G,
        CantorSetTasteGate_single_carrier_alignment_decode_encode I,
        CantorSetTasteGate_single_carrier_alignment_decode_encode D,
        CantorSetTasteGate_single_carrier_alignment_decode_encode R,
        CantorSetTasteGate_single_carrier_alignment_decode_encode E]

private theorem CantorSetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CantorSetUp} :
    CantorSetTasteGate_single_carrier_alignment_toEventFlow x =
        CantorSetTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CantorSetTasteGate_single_carrier_alignment_fromEventFlow
          (CantorSetTasteGate_single_carrier_alignment_toEventFlow x) =
        CantorSetTasteGate_single_carrier_alignment_fromEventFlow
          (CantorSetTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CantorSetTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CantorSetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CantorSetTasteGate_single_carrier_alignment_round_trip y)))

private theorem CantorSetTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CantorSetUp,
      CantorSetTasteGate_single_carrier_alignment_fields x =
          CantorSetTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ G₁ I₁ D₁ R₁ E₁ =>
      cases y with
      | mk T₂ G₂ I₂ D₂ R₂ E₂ =>
          cases hfields
          rfl

instance CantorSetTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CantorSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CantorSetTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CantorSetTasteGate_single_carrier_alignment_fromEventFlow

instance CantorSetTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CantorSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CantorSetTasteGate_single_carrier_alignment_fromEventFlow
          (CantorSetTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CantorSetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CantorSetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance CantorSetTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful CantorSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CantorSetTasteGate_single_carrier_alignment_fields
  field_faithful := CantorSetTasteGate_single_carrier_alignment_fields_faithful

theorem CantorSetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      CantorSetTasteGate_single_carrier_alignment_decodeBHist
          (CantorSetTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      CantorSetTasteGate_single_carrier_alignment_fields
          (CantorSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CantorSetTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.CantorSetUp
