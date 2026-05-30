import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionKleisliAdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionKleisliAdjunctionUp : Type where
  | mk (U B L A V S D R E H C P N : BHist) : CauchyCompletionKleisliAdjunctionUp
  deriving DecidableEq

def cauchyCompletionKleisliAdjunctionTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1, BMark.b0]

def cauchyCompletionKleisliAdjunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionKleisliAdjunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionKleisliAdjunctionEncodeBHist h

def cauchyCompletionKleisliAdjunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionKleisliAdjunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionKleisliAdjunctionDecodeBHist tail)

private theorem CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionKleisliAdjunctionDecodeBHist
          (cauchyCompletionKleisliAdjunctionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionKleisliAdjunctionFields :
    CauchyCompletionKleisliAdjunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionKleisliAdjunctionUp.mk U B L A V S D R E H C P N =>
      [U, B, L, A, V, S, D, R, E, H, C, P, N]

def cauchyCompletionKleisliAdjunctionToEventFlow :
    CauchyCompletionKleisliAdjunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionKleisliAdjunctionUp.mk U B L A V S D R E H C P N =>
      [cauchyCompletionKleisliAdjunctionTag,
        cauchyCompletionKleisliAdjunctionEncodeBHist U,
        cauchyCompletionKleisliAdjunctionEncodeBHist B,
        cauchyCompletionKleisliAdjunctionEncodeBHist L,
        cauchyCompletionKleisliAdjunctionEncodeBHist A,
        cauchyCompletionKleisliAdjunctionEncodeBHist V,
        cauchyCompletionKleisliAdjunctionEncodeBHist S,
        cauchyCompletionKleisliAdjunctionEncodeBHist D,
        cauchyCompletionKleisliAdjunctionEncodeBHist R,
        cauchyCompletionKleisliAdjunctionEncodeBHist E,
        cauchyCompletionKleisliAdjunctionEncodeBHist H,
        cauchyCompletionKleisliAdjunctionEncodeBHist C,
        cauchyCompletionKleisliAdjunctionEncodeBHist P,
        cauchyCompletionKleisliAdjunctionEncodeBHist N]

private def CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt index rest

def cauchyCompletionKleisliAdjunctionFromEventFlow :
    EventFlow → Option CauchyCompletionKleisliAdjunctionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchyCompletionKleisliAdjunctionUp.mk
          (cauchyCompletionKleisliAdjunctionDecodeBHist
            (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt 1 ef))
          (cauchyCompletionKleisliAdjunctionDecodeBHist
            (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt 2 ef))
          (cauchyCompletionKleisliAdjunctionDecodeBHist
            (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt 3 ef))
          (cauchyCompletionKleisliAdjunctionDecodeBHist
            (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt 4 ef))
          (cauchyCompletionKleisliAdjunctionDecodeBHist
            (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt 5 ef))
          (cauchyCompletionKleisliAdjunctionDecodeBHist
            (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt 6 ef))
          (cauchyCompletionKleisliAdjunctionDecodeBHist
            (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt 7 ef))
          (cauchyCompletionKleisliAdjunctionDecodeBHist
            (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt 8 ef))
          (cauchyCompletionKleisliAdjunctionDecodeBHist
            (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt 9 ef))
          (cauchyCompletionKleisliAdjunctionDecodeBHist
            (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt 10 ef))
          (cauchyCompletionKleisliAdjunctionDecodeBHist
            (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt 11 ef))
          (cauchyCompletionKleisliAdjunctionDecodeBHist
            (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt 12 ef))
          (cauchyCompletionKleisliAdjunctionDecodeBHist
            (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_eventAt 13 ef)))

private theorem CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionKleisliAdjunctionUp,
      cauchyCompletionKleisliAdjunctionFromEventFlow
          (cauchyCompletionKleisliAdjunctionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk U B L A V S D R E H C P N =>
      change
        some
          (CauchyCompletionKleisliAdjunctionUp.mk
            (cauchyCompletionKleisliAdjunctionDecodeBHist
              (cauchyCompletionKleisliAdjunctionEncodeBHist U))
            (cauchyCompletionKleisliAdjunctionDecodeBHist
              (cauchyCompletionKleisliAdjunctionEncodeBHist B))
            (cauchyCompletionKleisliAdjunctionDecodeBHist
              (cauchyCompletionKleisliAdjunctionEncodeBHist L))
            (cauchyCompletionKleisliAdjunctionDecodeBHist
              (cauchyCompletionKleisliAdjunctionEncodeBHist A))
            (cauchyCompletionKleisliAdjunctionDecodeBHist
              (cauchyCompletionKleisliAdjunctionEncodeBHist V))
            (cauchyCompletionKleisliAdjunctionDecodeBHist
              (cauchyCompletionKleisliAdjunctionEncodeBHist S))
            (cauchyCompletionKleisliAdjunctionDecodeBHist
              (cauchyCompletionKleisliAdjunctionEncodeBHist D))
            (cauchyCompletionKleisliAdjunctionDecodeBHist
              (cauchyCompletionKleisliAdjunctionEncodeBHist R))
            (cauchyCompletionKleisliAdjunctionDecodeBHist
              (cauchyCompletionKleisliAdjunctionEncodeBHist E))
            (cauchyCompletionKleisliAdjunctionDecodeBHist
              (cauchyCompletionKleisliAdjunctionEncodeBHist H))
            (cauchyCompletionKleisliAdjunctionDecodeBHist
              (cauchyCompletionKleisliAdjunctionEncodeBHist C))
            (cauchyCompletionKleisliAdjunctionDecodeBHist
              (cauchyCompletionKleisliAdjunctionEncodeBHist P))
            (cauchyCompletionKleisliAdjunctionDecodeBHist
              (cauchyCompletionKleisliAdjunctionEncodeBHist N))) =
          some (CauchyCompletionKleisliAdjunctionUp.mk U B L A V S D R E H C P N)
      rw [CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode U,
        CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode B,
        CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode L,
        CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode A,
        CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode V,
        CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode S,
        CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode D,
        CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode R,
        CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode E,
        CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode H,
        CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode C,
        CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode P,
        CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionKleisliAdjunctionUp} :
    cauchyCompletionKleisliAdjunctionToEventFlow x =
        cauchyCompletionKleisliAdjunctionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionKleisliAdjunctionFromEventFlow
          (cauchyCompletionKleisliAdjunctionToEventFlow x) =
        cauchyCompletionKleisliAdjunctionFromEventFlow
          (cauchyCompletionKleisliAdjunctionToEventFlow y) :=
    congrArg cauchyCompletionKleisliAdjunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchyCompletionKleisliAdjunctionUp,
      cauchyCompletionKleisliAdjunctionFields x =
          cauchyCompletionKleisliAdjunctionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ B₁ L₁ A₁ V₁ S₁ D₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk U₂ B₂ L₂ A₂ V₂ S₂ D₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance cauchyCompletionKleisliAdjunctionBHistCarrier :
    BHistCarrier CauchyCompletionKleisliAdjunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionKleisliAdjunctionToEventFlow
  fromEventFlow := cauchyCompletionKleisliAdjunctionFromEventFlow

instance cauchyCompletionKleisliAdjunctionChapterTasteGate :
    ChapterTasteGate CauchyCompletionKleisliAdjunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionKleisliAdjunctionFromEventFlow
          (cauchyCompletionKleisliAdjunctionToEventFlow x) =
        some x
    exact CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance cauchyCompletionKleisliAdjunctionFieldFaithful :
    FieldFaithful CauchyCompletionKleisliAdjunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionKleisliAdjunctionFields
  field_faithful :=
    CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_fields_faithful

instance cauchyCompletionKleisliAdjunctionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyCompletionKleisliAdjunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyCompletionKleisliAdjunctionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      CauchyCompletionKleisliAdjunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyCompletionKleisliAdjunctionUp) ∧
      Nonempty (FieldFaithful CauchyCompletionKleisliAdjunctionUp) ∧
        Nonempty
          (BEDC.Meta.TasteGate.Nontrivial CauchyCompletionKleisliAdjunctionUp) ∧
          (∀ h : BHist,
            cauchyCompletionKleisliAdjunctionDecodeBHist
                (cauchyCompletionKleisliAdjunctionEncodeBHist h) =
              h) ∧
            (∀ x : CauchyCompletionKleisliAdjunctionUp,
              cauchyCompletionKleisliAdjunctionFromEventFlow
                  (cauchyCompletionKleisliAdjunctionToEventFlow x) =
                some x) ∧
              cauchyCompletionKleisliAdjunctionEncodeBHist BHist.Empty =
                ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨cauchyCompletionKleisliAdjunctionChapterTasteGate⟩,
      ⟨cauchyCompletionKleisliAdjunctionFieldFaithful⟩,
      ⟨cauchyCompletionKleisliAdjunctionNontrivial⟩,
      CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_decode,
      CauchyCompletionKleisliAdjunctionTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.CauchyCompletionKleisliAdjunctionUp
