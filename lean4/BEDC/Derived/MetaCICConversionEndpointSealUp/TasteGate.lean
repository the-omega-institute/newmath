import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICConversionEndpointSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICConversionEndpointSealUp : Type where
  | mk (B F D T O H C P N : BHist) : MetaCICConversionEndpointSealUp

def metaCICConversionEndpointSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICConversionEndpointSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICConversionEndpointSealEncodeBHist h

def metaCICConversionEndpointSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICConversionEndpointSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICConversionEndpointSealDecodeBHist tail)

private theorem metaCICConversionEndpointSealDecode_encode :
    ∀ h : BHist,
      metaCICConversionEndpointSealDecodeBHist
          (metaCICConversionEndpointSealEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICConversionEndpointSealFields :
    MetaCICConversionEndpointSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICConversionEndpointSealUp.mk B F D T O H C P N =>
      [B, F, D, T, O, H, C, P, N]

def metaCICConversionEndpointSealToEventFlow :
    MetaCICConversionEndpointSealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (metaCICConversionEndpointSealFields x).map metaCICConversionEndpointSealEncodeBHist

private def metaCICConversionEndpointSealEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metaCICConversionEndpointSealEventAtDefault index rest

def metaCICConversionEndpointSealFromEventFlow
    (ef : EventFlow) : Option MetaCICConversionEndpointSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICConversionEndpointSealUp.mk
      (metaCICConversionEndpointSealDecodeBHist
        (metaCICConversionEndpointSealEventAtDefault 0 ef))
      (metaCICConversionEndpointSealDecodeBHist
        (metaCICConversionEndpointSealEventAtDefault 1 ef))
      (metaCICConversionEndpointSealDecodeBHist
        (metaCICConversionEndpointSealEventAtDefault 2 ef))
      (metaCICConversionEndpointSealDecodeBHist
        (metaCICConversionEndpointSealEventAtDefault 3 ef))
      (metaCICConversionEndpointSealDecodeBHist
        (metaCICConversionEndpointSealEventAtDefault 4 ef))
      (metaCICConversionEndpointSealDecodeBHist
        (metaCICConversionEndpointSealEventAtDefault 5 ef))
      (metaCICConversionEndpointSealDecodeBHist
        (metaCICConversionEndpointSealEventAtDefault 6 ef))
      (metaCICConversionEndpointSealDecodeBHist
        (metaCICConversionEndpointSealEventAtDefault 7 ef))
      (metaCICConversionEndpointSealDecodeBHist
        (metaCICConversionEndpointSealEventAtDefault 8 ef)))

private theorem metaCICConversionEndpointSeal_round_trip :
    ∀ x : MetaCICConversionEndpointSealUp,
      metaCICConversionEndpointSealFromEventFlow
          (metaCICConversionEndpointSealToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B F D T O H C P N =>
      change
        some
          (MetaCICConversionEndpointSealUp.mk
            (metaCICConversionEndpointSealDecodeBHist
              (metaCICConversionEndpointSealEncodeBHist B))
            (metaCICConversionEndpointSealDecodeBHist
              (metaCICConversionEndpointSealEncodeBHist F))
            (metaCICConversionEndpointSealDecodeBHist
              (metaCICConversionEndpointSealEncodeBHist D))
            (metaCICConversionEndpointSealDecodeBHist
              (metaCICConversionEndpointSealEncodeBHist T))
            (metaCICConversionEndpointSealDecodeBHist
              (metaCICConversionEndpointSealEncodeBHist O))
            (metaCICConversionEndpointSealDecodeBHist
              (metaCICConversionEndpointSealEncodeBHist H))
            (metaCICConversionEndpointSealDecodeBHist
              (metaCICConversionEndpointSealEncodeBHist C))
            (metaCICConversionEndpointSealDecodeBHist
              (metaCICConversionEndpointSealEncodeBHist P))
            (metaCICConversionEndpointSealDecodeBHist
              (metaCICConversionEndpointSealEncodeBHist N))) =
          some (MetaCICConversionEndpointSealUp.mk B F D T O H C P N)
      rw [metaCICConversionEndpointSealDecode_encode B,
        metaCICConversionEndpointSealDecode_encode F,
        metaCICConversionEndpointSealDecode_encode D,
        metaCICConversionEndpointSealDecode_encode T,
        metaCICConversionEndpointSealDecode_encode O,
        metaCICConversionEndpointSealDecode_encode H,
        metaCICConversionEndpointSealDecode_encode C,
        metaCICConversionEndpointSealDecode_encode P,
        metaCICConversionEndpointSealDecode_encode N]

private theorem metaCICConversionEndpointSealToEventFlow_injective
    {x y : MetaCICConversionEndpointSealUp} :
    metaCICConversionEndpointSealToEventFlow x =
        metaCICConversionEndpointSealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICConversionEndpointSealFromEventFlow
          (metaCICConversionEndpointSealToEventFlow x) =
        metaCICConversionEndpointSealFromEventFlow
          (metaCICConversionEndpointSealToEventFlow y) :=
    congrArg metaCICConversionEndpointSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICConversionEndpointSeal_round_trip x).symm
      (Eq.trans hread (metaCICConversionEndpointSeal_round_trip y)))

private theorem metaCICConversionEndpointSeal_fields_faithful :
    ∀ x y : MetaCICConversionEndpointSealUp,
      metaCICConversionEndpointSealFields x = metaCICConversionEndpointSealFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ F₁ D₁ T₁ O₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ F₂ D₂ T₂ O₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hB t0
          injection t0 with hF t1
          injection t1 with hD t2
          injection t2 with hT t3
          injection t3 with hO t4
          injection t4 with hH t5
          injection t5 with hC t6
          injection t6 with hP t7
          injection t7 with hN _
          subst hB
          subst hF
          subst hD
          subst hT
          subst hO
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance metaCICConversionEndpointSealBHistCarrier :
    BHistCarrier MetaCICConversionEndpointSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICConversionEndpointSealToEventFlow
  fromEventFlow := metaCICConversionEndpointSealFromEventFlow

instance metaCICConversionEndpointSealChapterTasteGate :
    ChapterTasteGate MetaCICConversionEndpointSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICConversionEndpointSealFromEventFlow
          (metaCICConversionEndpointSealToEventFlow x) =
        some x
    exact metaCICConversionEndpointSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICConversionEndpointSealToEventFlow_injective heq)

instance metaCICConversionEndpointSealFieldFaithful :
    FieldFaithful MetaCICConversionEndpointSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICConversionEndpointSealFields
  field_faithful := metaCICConversionEndpointSeal_fields_faithful

instance metaCICConversionEndpointSealNontrivial :
    Nontrivial MetaCICConversionEndpointSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICConversionEndpointSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICConversionEndpointSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def metaCICConversionEndpointSeal_taste_gate :
    ChapterTasteGate MetaCICConversionEndpointSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICConversionEndpointSealChapterTasteGate

theorem MetaCICConversionEndpointSealTasteGate_single_carrier_alignment :
    (forall h : BHist,
      metaCICConversionEndpointSealDecodeBHist
          (metaCICConversionEndpointSealEncodeBHist h) = h) /\
      (forall x : MetaCICConversionEndpointSealUp,
        metaCICConversionEndpointSealFromEventFlow
            (metaCICConversionEndpointSealToEventFlow x) = some x) /\
      (forall x y : MetaCICConversionEndpointSealUp,
        metaCICConversionEndpointSealToEventFlow x =
            metaCICConversionEndpointSealToEventFlow y ->
          x = y) /\
      metaCICConversionEndpointSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaCICConversionEndpointSealDecode_encode
  · constructor
    · exact metaCICConversionEndpointSeal_round_trip
    · constructor
      · intro x y heq
        exact metaCICConversionEndpointSealToEventFlow_injective heq
      · rfl

end BEDC.Derived.MetaCICConversionEndpointSealUp
