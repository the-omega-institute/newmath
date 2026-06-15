import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveCompactUniformFanUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveCompactUniformFanUp : Type where
  | mk (K B T W D M U E H C P N : BHist) : ConstructiveCompactUniformFanUp
  deriving DecidableEq

def constructiveCompactUniformFanEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveCompactUniformFanEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveCompactUniformFanEncodeBHist h

def constructiveCompactUniformFanDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveCompactUniformFanDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveCompactUniformFanDecodeBHist tail)

private theorem ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      constructiveCompactUniformFanDecodeBHist
        (constructiveCompactUniformFanEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveCompactUniformFanFields :
    ConstructiveCompactUniformFanUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveCompactUniformFanUp.mk K B T W D M U E H C P N =>
      [K, B, T, W, D, M, U, E, H, C, P, N]

def constructiveCompactUniformFanToEventFlow :
    ConstructiveCompactUniformFanUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (constructiveCompactUniformFanFields x).map constructiveCompactUniformFanEncodeBHist

private def constructiveCompactUniformFanEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveCompactUniformFanEventAtDefault index rest

def constructiveCompactUniformFanFromEventFlow
    (ef : EventFlow) : Option ConstructiveCompactUniformFanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveCompactUniformFanUp.mk
      (constructiveCompactUniformFanDecodeBHist
        (constructiveCompactUniformFanEventAtDefault 0 ef))
      (constructiveCompactUniformFanDecodeBHist
        (constructiveCompactUniformFanEventAtDefault 1 ef))
      (constructiveCompactUniformFanDecodeBHist
        (constructiveCompactUniformFanEventAtDefault 2 ef))
      (constructiveCompactUniformFanDecodeBHist
        (constructiveCompactUniformFanEventAtDefault 3 ef))
      (constructiveCompactUniformFanDecodeBHist
        (constructiveCompactUniformFanEventAtDefault 4 ef))
      (constructiveCompactUniformFanDecodeBHist
        (constructiveCompactUniformFanEventAtDefault 5 ef))
      (constructiveCompactUniformFanDecodeBHist
        (constructiveCompactUniformFanEventAtDefault 6 ef))
      (constructiveCompactUniformFanDecodeBHist
        (constructiveCompactUniformFanEventAtDefault 7 ef))
      (constructiveCompactUniformFanDecodeBHist
        (constructiveCompactUniformFanEventAtDefault 8 ef))
      (constructiveCompactUniformFanDecodeBHist
        (constructiveCompactUniformFanEventAtDefault 9 ef))
      (constructiveCompactUniformFanDecodeBHist
        (constructiveCompactUniformFanEventAtDefault 10 ef))
      (constructiveCompactUniformFanDecodeBHist
        (constructiveCompactUniformFanEventAtDefault 11 ef)))

private theorem ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConstructiveCompactUniformFanUp,
      constructiveCompactUniformFanFromEventFlow
        (constructiveCompactUniformFanToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K B T W D M U E H C P N =>
      change
        some
          (ConstructiveCompactUniformFanUp.mk
            (constructiveCompactUniformFanDecodeBHist
              (constructiveCompactUniformFanEncodeBHist K))
            (constructiveCompactUniformFanDecodeBHist
              (constructiveCompactUniformFanEncodeBHist B))
            (constructiveCompactUniformFanDecodeBHist
              (constructiveCompactUniformFanEncodeBHist T))
            (constructiveCompactUniformFanDecodeBHist
              (constructiveCompactUniformFanEncodeBHist W))
            (constructiveCompactUniformFanDecodeBHist
              (constructiveCompactUniformFanEncodeBHist D))
            (constructiveCompactUniformFanDecodeBHist
              (constructiveCompactUniformFanEncodeBHist M))
            (constructiveCompactUniformFanDecodeBHist
              (constructiveCompactUniformFanEncodeBHist U))
            (constructiveCompactUniformFanDecodeBHist
              (constructiveCompactUniformFanEncodeBHist E))
            (constructiveCompactUniformFanDecodeBHist
              (constructiveCompactUniformFanEncodeBHist H))
            (constructiveCompactUniformFanDecodeBHist
              (constructiveCompactUniformFanEncodeBHist C))
            (constructiveCompactUniformFanDecodeBHist
              (constructiveCompactUniformFanEncodeBHist P))
            (constructiveCompactUniformFanDecodeBHist
              (constructiveCompactUniformFanEncodeBHist N))) =
          some (ConstructiveCompactUniformFanUp.mk K B T W D M U E H C P N)
      rw [ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode K,
        ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode B,
        ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode T,
        ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode W,
        ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode D,
        ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode M,
        ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode U,
        ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode E,
        ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode H,
        ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode C,
        ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode P,
        ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode N]

private theorem ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_injective
    {x y : ConstructiveCompactUniformFanUp} :
    constructiveCompactUniformFanToEventFlow x =
      constructiveCompactUniformFanToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveCompactUniformFanFromEventFlow
          (constructiveCompactUniformFanToEventFlow x) =
        constructiveCompactUniformFanFromEventFlow
          (constructiveCompactUniformFanToEventFlow y) :=
    congrArg constructiveCompactUniformFanFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_round_trip y)))

private theorem ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_fields :
    ∀ x y : ConstructiveCompactUniformFanUp,
      constructiveCompactUniformFanFields x =
        constructiveCompactUniformFanFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K₁ B₁ T₁ W₁ D₁ M₁ U₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk K₂ B₂ T₂ W₂ D₂ M₂ U₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hK tail0
          injection tail0 with hB tail1
          injection tail1 with hT tail2
          injection tail2 with hW tail3
          injection tail3 with hD tail4
          injection tail4 with hM tail5
          injection tail5 with hU tail6
          injection tail6 with hE tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          subst hK
          subst hB
          subst hT
          subst hW
          subst hD
          subst hM
          subst hU
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance constructiveCompactUniformFanBHistCarrier :
    BHistCarrier ConstructiveCompactUniformFanUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveCompactUniformFanToEventFlow
  fromEventFlow := constructiveCompactUniformFanFromEventFlow

instance constructiveCompactUniformFanChapterTasteGate :
    ChapterTasteGate ConstructiveCompactUniformFanUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      constructiveCompactUniformFanFromEventFlow
        (constructiveCompactUniformFanToEventFlow x) = some x
    exact ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_injective heq)

instance constructiveCompactUniformFanFieldFaithful :
    FieldFaithful ConstructiveCompactUniformFanUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := constructiveCompactUniformFanFields
  field_faithful := ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_fields

instance constructiveCompactUniformFanNontrivial : Nontrivial ConstructiveCompactUniformFanUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConstructiveCompactUniformFanUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ConstructiveCompactUniformFanUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ConstructiveCompactUniformFanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveCompactUniformFanChapterTasteGate

def taste_gate_witness : FieldFaithful ConstructiveCompactUniformFanUp :=
  -- BEDC touchpoint anchor: BHist BMark
  constructiveCompactUniformFanFieldFaithful

theorem ConstructiveCompactUniformFanTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        constructiveCompactUniformFanDecodeBHist
          (constructiveCompactUniformFanEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ConstructiveCompactUniformFanUp) ∧
        Nonempty (ChapterTasteGate ConstructiveCompactUniformFanUp) ∧
          Nonempty (FieldFaithful ConstructiveCompactUniformFanUp) ∧
            Nonempty (BEDC.Meta.TasteGate.Nontrivial ConstructiveCompactUniformFanUp) ∧
              constructiveCompactUniformFanEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨ConstructiveCompactUniformFanTasteGate_single_carrier_alignment_decode,
      ⟨constructiveCompactUniformFanBHistCarrier⟩,
      ⟨constructiveCompactUniformFanChapterTasteGate⟩,
      ⟨constructiveCompactUniformFanFieldFaithful⟩,
      ⟨constructiveCompactUniformFanNontrivial⟩,
      rfl⟩

end BEDC.Derived.ConstructiveCompactUniformFanUp
