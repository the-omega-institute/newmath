import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailEstimateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailEstimateUp : Type where
  | mk (T D R E B H C P N : BHist) : CauchyTailEstimateUp
  deriving DecidableEq

def CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist h

def CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CauchyTailEstimateTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
        (CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchyTailEstimateTasteGate_single_carrier_alignment_fields :
    CauchyTailEstimateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailEstimateUp.mk T D R E B H C P N => [T, D, R, E, B, H, C, P, N]

def CauchyTailEstimateTasteGate_single_carrier_alignment_toEventFlow :
    CauchyTailEstimateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (CauchyTailEstimateTasteGate_single_carrier_alignment_fields x).map
        CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist

private def CauchyTailEstimateTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyTailEstimateTasteGate_single_carrier_alignment_eventAtDefault index rest

def CauchyTailEstimateTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option CauchyTailEstimateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyTailEstimateUp.mk
      (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
        (CauchyTailEstimateTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
      (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
        (CauchyTailEstimateTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
        (CauchyTailEstimateTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
      (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
        (CauchyTailEstimateTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
        (CauchyTailEstimateTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
      (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
        (CauchyTailEstimateTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
        (CauchyTailEstimateTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
      (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
        (CauchyTailEstimateTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
        (CauchyTailEstimateTasteGate_single_carrier_alignment_eventAtDefault 8 ef)))

private theorem CauchyTailEstimateTasteGate_single_carrier_alignment_round_trip
    (x : CauchyTailEstimateUp) :
    CauchyTailEstimateTasteGate_single_carrier_alignment_fromEventFlow
      (CauchyTailEstimateTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T D R E B H C P N =>
      change
        some
          (CauchyTailEstimateUp.mk
            (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
              (CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist T))
            (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
              (CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist D))
            (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
              (CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist R))
            (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
              (CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist E))
            (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
              (CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist B))
            (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
              (CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist H))
            (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
              (CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist C))
            (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
              (CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist P))
            (CauchyTailEstimateTasteGate_single_carrier_alignment_decodeBHist
              (CauchyTailEstimateTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CauchyTailEstimateUp.mk T D R E B H C P N)
      rw [CauchyTailEstimateTasteGate_single_carrier_alignment_decode_encode T,
        CauchyTailEstimateTasteGate_single_carrier_alignment_decode_encode D,
        CauchyTailEstimateTasteGate_single_carrier_alignment_decode_encode R,
        CauchyTailEstimateTasteGate_single_carrier_alignment_decode_encode E,
        CauchyTailEstimateTasteGate_single_carrier_alignment_decode_encode B,
        CauchyTailEstimateTasteGate_single_carrier_alignment_decode_encode H,
        CauchyTailEstimateTasteGate_single_carrier_alignment_decode_encode C,
        CauchyTailEstimateTasteGate_single_carrier_alignment_decode_encode P,
        CauchyTailEstimateTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyTailEstimateTasteGate_single_carrier_alignment_injective
    {x y : CauchyTailEstimateUp} :
    CauchyTailEstimateTasteGate_single_carrier_alignment_toEventFlow x =
      CauchyTailEstimateTasteGate_single_carrier_alignment_toEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CauchyTailEstimateTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyTailEstimateTasteGate_single_carrier_alignment_toEventFlow x) =
        CauchyTailEstimateTasteGate_single_carrier_alignment_fromEventFlow
          (CauchyTailEstimateTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CauchyTailEstimateTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyTailEstimateTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyTailEstimateTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyTailEstimateTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CauchyTailEstimateUp,
      CauchyTailEstimateTasteGate_single_carrier_alignment_fields x =
        CauchyTailEstimateTasteGate_single_carrier_alignment_fields y →
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ D₁ R₁ E₁ B₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ D₂ R₂ E₂ B₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance CauchyTailEstimateTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CauchyTailEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CauchyTailEstimateTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CauchyTailEstimateTasteGate_single_carrier_alignment_fromEventFlow

instance CauchyTailEstimateTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful CauchyTailEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CauchyTailEstimateTasteGate_single_carrier_alignment_fields
  field_faithful := CauchyTailEstimateTasteGate_single_carrier_alignment_field_faithful

instance CauchyTailEstimateTasteGate_single_carrier_alignment_Nontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyTailEstimateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyTailEstimateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyTailEstimateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyTailEstimateTasteGate_single_carrier_alignment :
    ChapterTasteGate CauchyTailEstimateUp := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change
      CauchyTailEstimateTasteGate_single_carrier_alignment_fromEventFlow
        (CauchyTailEstimateTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact CauchyTailEstimateTasteGate_single_carrier_alignment_round_trip x
  · intro x y hxy heq
    exact hxy (CauchyTailEstimateTasteGate_single_carrier_alignment_injective heq)

instance CauchyTailEstimateTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CauchyTailEstimateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CauchyTailEstimateTasteGate_single_carrier_alignment

def CauchyTailEstimateTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyTailEstimateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CauchyTailEstimateTasteGate_single_carrier_alignment

end BEDC.Derived.CauchyTailEstimateUp
