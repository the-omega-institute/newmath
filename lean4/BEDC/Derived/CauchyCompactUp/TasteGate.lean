import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompactUp : Type where
  | mk (M L T S D E H C P N : BHist) : CauchyCompactUp
  deriving DecidableEq

def CauchyCompactTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CauchyCompactTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CauchyCompactTasteGate_single_carrier_alignment_encodeBHist h

def CauchyCompactTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchyCompactTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
          (CauchyCompactTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchyCompactTasteGate_single_carrier_alignment_fields :
    CauchyCompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompactUp.mk M L T S D E H C P N => [M, L, T, S, D, E, H, C, P, N]

def CauchyCompactTasteGate_single_carrier_alignment_toEventFlow :
    CauchyCompactUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (CauchyCompactTasteGate_single_carrier_alignment_fields x).map
      CauchyCompactTasteGate_single_carrier_alignment_encodeBHist

private def CauchyCompactTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyCompactTasteGate_single_carrier_alignment_eventAt index rest

def CauchyCompactTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option CauchyCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompactUp.mk
      (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
        (CauchyCompactTasteGate_single_carrier_alignment_eventAt 0 ef))
      (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
        (CauchyCompactTasteGate_single_carrier_alignment_eventAt 1 ef))
      (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
        (CauchyCompactTasteGate_single_carrier_alignment_eventAt 2 ef))
      (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
        (CauchyCompactTasteGate_single_carrier_alignment_eventAt 3 ef))
      (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
        (CauchyCompactTasteGate_single_carrier_alignment_eventAt 4 ef))
      (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
        (CauchyCompactTasteGate_single_carrier_alignment_eventAt 5 ef))
      (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
        (CauchyCompactTasteGate_single_carrier_alignment_eventAt 6 ef))
      (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
        (CauchyCompactTasteGate_single_carrier_alignment_eventAt 7 ef))
      (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
        (CauchyCompactTasteGate_single_carrier_alignment_eventAt 8 ef))
      (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
        (CauchyCompactTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem CauchyCompactTasteGate_single_carrier_alignment_round_trip
    (x : CauchyCompactUp) :
    CauchyCompactTasteGate_single_carrier_alignment_fromEventFlow
        (CauchyCompactTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M L T S D E H C P N =>
      change
        some
          (CauchyCompactUp.mk
            (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompactTasteGate_single_carrier_alignment_encodeBHist M))
            (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompactTasteGate_single_carrier_alignment_encodeBHist L))
            (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompactTasteGate_single_carrier_alignment_encodeBHist T))
            (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompactTasteGate_single_carrier_alignment_encodeBHist S))
            (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompactTasteGate_single_carrier_alignment_encodeBHist D))
            (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompactTasteGate_single_carrier_alignment_encodeBHist E))
            (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompactTasteGate_single_carrier_alignment_encodeBHist H))
            (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompactTasteGate_single_carrier_alignment_encodeBHist C))
            (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompactTasteGate_single_carrier_alignment_encodeBHist P))
            (CauchyCompactTasteGate_single_carrier_alignment_decodeBHist
              (CauchyCompactTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CauchyCompactUp.mk M L T S D E H C P N)
      rw [CauchyCompactTasteGate_single_carrier_alignment_decode_encode M,
        CauchyCompactTasteGate_single_carrier_alignment_decode_encode L,
        CauchyCompactTasteGate_single_carrier_alignment_decode_encode T,
        CauchyCompactTasteGate_single_carrier_alignment_decode_encode S,
        CauchyCompactTasteGate_single_carrier_alignment_decode_encode D,
        CauchyCompactTasteGate_single_carrier_alignment_decode_encode E,
        CauchyCompactTasteGate_single_carrier_alignment_decode_encode H,
        CauchyCompactTasteGate_single_carrier_alignment_decode_encode C,
        CauchyCompactTasteGate_single_carrier_alignment_decode_encode P,
        CauchyCompactTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyCompactTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompactUp} :
    CauchyCompactTasteGate_single_carrier_alignment_toEventFlow x =
        CauchyCompactTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CauchyCompactTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyCompactTasteGate_single_carrier_alignment_toEventFlow x) =
        CauchyCompactTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyCompactTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CauchyCompactTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyCompactTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyCompactTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCompactTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyCompactUp,
      CauchyCompactTasteGate_single_carrier_alignment_fields x =
          CauchyCompactTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ L₁ T₁ S₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ L₂ T₂ S₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance CauchyCompactTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CauchyCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyCompactTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyCompactTasteGate_single_carrier_alignment_fromEventFlow

instance CauchyCompactTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CauchyCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CauchyCompactTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyCompactTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CauchyCompactTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCompactTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance CauchyCompactTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful CauchyCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CauchyCompactTasteGate_single_carrier_alignment_fields
  field_faithful := CauchyCompactTasteGate_single_carrier_alignment_fields_faithful

def CauchyCompactTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyCompactUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CauchyCompactTasteGate_single_carrier_alignment_ChapterTasteGate

theorem CauchyCompactTasteGate_single_carrier_alignment :
    ChapterTasteGate CauchyCompactUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact CauchyCompactTasteGate_single_carrier_alignment_ChapterTasteGate

end BEDC.Derived.CauchyCompactUp
