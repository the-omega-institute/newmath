import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICDecidableConversionFrontierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICDecidableConversionFrontierUp : Type where
  | mk (D N B S K Q O H C P L : BHist) : MetaCICDecidableConversionFrontierUp
  deriving DecidableEq

def metaCICDecidableConversionFrontierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICDecidableConversionFrontierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICDecidableConversionFrontierEncodeBHist h

def metaCICDecidableConversionFrontierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICDecidableConversionFrontierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICDecidableConversionFrontierDecodeBHist tail)

private theorem MetaCICDecidableConversionFrontierTasteGate_decode :
    ∀ h : BHist,
      metaCICDecidableConversionFrontierDecodeBHist
        (metaCICDecidableConversionFrontierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaCICDecidableConversionFrontierFields :
    MetaCICDecidableConversionFrontierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICDecidableConversionFrontierUp.mk D N B S K Q O H C P L =>
      [D, N, B, S, K, Q, O, H, C, P, L]

def metaCICDecidableConversionFrontierToEventFlow :
    MetaCICDecidableConversionFrontierUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (metaCICDecidableConversionFrontierFields x).map
      metaCICDecidableConversionFrontierEncodeBHist

private def metaCICDecidableConversionFrontierEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metaCICDecidableConversionFrontierEventAtDefault index rest

def metaCICDecidableConversionFrontierFromEventFlow
    (ef : EventFlow) : Option MetaCICDecidableConversionFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICDecidableConversionFrontierUp.mk
      (metaCICDecidableConversionFrontierDecodeBHist
        (metaCICDecidableConversionFrontierEventAtDefault 0 ef))
      (metaCICDecidableConversionFrontierDecodeBHist
        (metaCICDecidableConversionFrontierEventAtDefault 1 ef))
      (metaCICDecidableConversionFrontierDecodeBHist
        (metaCICDecidableConversionFrontierEventAtDefault 2 ef))
      (metaCICDecidableConversionFrontierDecodeBHist
        (metaCICDecidableConversionFrontierEventAtDefault 3 ef))
      (metaCICDecidableConversionFrontierDecodeBHist
        (metaCICDecidableConversionFrontierEventAtDefault 4 ef))
      (metaCICDecidableConversionFrontierDecodeBHist
        (metaCICDecidableConversionFrontierEventAtDefault 5 ef))
      (metaCICDecidableConversionFrontierDecodeBHist
        (metaCICDecidableConversionFrontierEventAtDefault 6 ef))
      (metaCICDecidableConversionFrontierDecodeBHist
        (metaCICDecidableConversionFrontierEventAtDefault 7 ef))
      (metaCICDecidableConversionFrontierDecodeBHist
        (metaCICDecidableConversionFrontierEventAtDefault 8 ef))
      (metaCICDecidableConversionFrontierDecodeBHist
        (metaCICDecidableConversionFrontierEventAtDefault 9 ef))
      (metaCICDecidableConversionFrontierDecodeBHist
        (metaCICDecidableConversionFrontierEventAtDefault 10 ef)))

private theorem MetaCICDecidableConversionFrontierTasteGate_round_trip :
    ∀ x : MetaCICDecidableConversionFrontierUp,
      metaCICDecidableConversionFrontierFromEventFlow
        (metaCICDecidableConversionFrontierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D N B S K Q O H C P L =>
      change
        some
          (MetaCICDecidableConversionFrontierUp.mk
            (metaCICDecidableConversionFrontierDecodeBHist
              (metaCICDecidableConversionFrontierEncodeBHist D))
            (metaCICDecidableConversionFrontierDecodeBHist
              (metaCICDecidableConversionFrontierEncodeBHist N))
            (metaCICDecidableConversionFrontierDecodeBHist
              (metaCICDecidableConversionFrontierEncodeBHist B))
            (metaCICDecidableConversionFrontierDecodeBHist
              (metaCICDecidableConversionFrontierEncodeBHist S))
            (metaCICDecidableConversionFrontierDecodeBHist
              (metaCICDecidableConversionFrontierEncodeBHist K))
            (metaCICDecidableConversionFrontierDecodeBHist
              (metaCICDecidableConversionFrontierEncodeBHist Q))
            (metaCICDecidableConversionFrontierDecodeBHist
              (metaCICDecidableConversionFrontierEncodeBHist O))
            (metaCICDecidableConversionFrontierDecodeBHist
              (metaCICDecidableConversionFrontierEncodeBHist H))
            (metaCICDecidableConversionFrontierDecodeBHist
              (metaCICDecidableConversionFrontierEncodeBHist C))
            (metaCICDecidableConversionFrontierDecodeBHist
              (metaCICDecidableConversionFrontierEncodeBHist P))
            (metaCICDecidableConversionFrontierDecodeBHist
              (metaCICDecidableConversionFrontierEncodeBHist L))) =
          some (MetaCICDecidableConversionFrontierUp.mk D N B S K Q O H C P L)
      rw [MetaCICDecidableConversionFrontierTasteGate_decode D,
        MetaCICDecidableConversionFrontierTasteGate_decode N,
        MetaCICDecidableConversionFrontierTasteGate_decode B,
        MetaCICDecidableConversionFrontierTasteGate_decode S,
        MetaCICDecidableConversionFrontierTasteGate_decode K,
        MetaCICDecidableConversionFrontierTasteGate_decode Q,
        MetaCICDecidableConversionFrontierTasteGate_decode O,
        MetaCICDecidableConversionFrontierTasteGate_decode H,
        MetaCICDecidableConversionFrontierTasteGate_decode C,
        MetaCICDecidableConversionFrontierTasteGate_decode P,
        MetaCICDecidableConversionFrontierTasteGate_decode L]

private theorem MetaCICDecidableConversionFrontierTasteGate_toEventFlow_injective
    {x y : MetaCICDecidableConversionFrontierUp} :
    metaCICDecidableConversionFrontierToEventFlow x =
        metaCICDecidableConversionFrontierToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICDecidableConversionFrontierFromEventFlow
          (metaCICDecidableConversionFrontierToEventFlow x) =
        metaCICDecidableConversionFrontierFromEventFlow
          (metaCICDecidableConversionFrontierToEventFlow y) :=
    congrArg metaCICDecidableConversionFrontierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MetaCICDecidableConversionFrontierTasteGate_round_trip x).symm
      (Eq.trans hread
        (MetaCICDecidableConversionFrontierTasteGate_round_trip y)))

private theorem MetaCICDecidableConversionFrontierTasteGate_fields :
    ∀ x y : MetaCICDecidableConversionFrontierUp,
      metaCICDecidableConversionFrontierFields x =
          metaCICDecidableConversionFrontierFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D₁ N₁ B₁ S₁ K₁ Q₁ O₁ H₁ C₁ P₁ L₁ =>
      cases y with
      | mk D₂ N₂ B₂ S₂ K₂ Q₂ O₂ H₂ C₂ P₂ L₂ =>
          cases hfields
          rfl

instance metaCICDecidableConversionFrontierBHistCarrier :
    BHistCarrier MetaCICDecidableConversionFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICDecidableConversionFrontierToEventFlow
  fromEventFlow := metaCICDecidableConversionFrontierFromEventFlow

instance metaCICDecidableConversionFrontierChapterTasteGate :
    ChapterTasteGate MetaCICDecidableConversionFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICDecidableConversionFrontierFromEventFlow
          (metaCICDecidableConversionFrontierToEventFlow x) =
        some x
    exact MetaCICDecidableConversionFrontierTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MetaCICDecidableConversionFrontierTasteGate_toEventFlow_injective heq)

instance metaCICDecidableConversionFrontierFieldFaithful :
    FieldFaithful MetaCICDecidableConversionFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICDecidableConversionFrontierFields
  field_faithful := MetaCICDecidableConversionFrontierTasteGate_fields

instance metaCICDecidableConversionFrontierNontrivial :
    Nontrivial MetaCICDecidableConversionFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICDecidableConversionFrontierUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      MetaCICDecidableConversionFrontierUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICDecidableConversionFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICDecidableConversionFrontierChapterTasteGate

theorem MetaCICDecidableConversionFrontierTasteGate_single_carrier_alignment :
    let base :=
      MetaCICDecidableConversionFrontierUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty
    let shifted :=
      MetaCICDecidableConversionFrontierUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty
    Nonempty (ChapterTasteGate MetaCICDecidableConversionFrontierUp) ∧
      Nonempty (BHistCarrier MetaCICDecidableConversionFrontierUp) ∧
        metaCICDecidableConversionFrontierFields base ≠
          metaCICDecidableConversionFrontierFields shifted := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact ⟨metaCICDecidableConversionFrontierChapterTasteGate⟩
  · constructor
    · exact ⟨metaCICDecidableConversionFrontierBHistCarrier⟩
    · intro sameFields
      cases sameFields

end BEDC.Derived.MetaCICDecidableConversionFrontierUp
