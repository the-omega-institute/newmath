import BEDC.Derived.AssouadSnowflakeEmbeddingUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AssouadSnowflakeEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

private def assouadSnowflakeEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: assouadSnowflakeEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: assouadSnowflakeEmbeddingEncodeBHist h

private def assouadSnowflakeEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (assouadSnowflakeEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (assouadSnowflakeEmbeddingDecodeBHist tail)

private theorem AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def assouadSnowflakeEmbeddingFields :
    AssouadSnowflakeEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AssouadSnowflakeEmbeddingUp.mk M D A S E B Q R H C P N =>
      [M, D, A, S, E, B, Q, R, H, C, P, N]

private def assouadSnowflakeEmbeddingToEventFlow :
    AssouadSnowflakeEmbeddingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (assouadSnowflakeEmbeddingFields x).map assouadSnowflakeEmbeddingEncodeBHist

private def assouadSnowflakeEmbeddingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => assouadSnowflakeEmbeddingEventAtDefault index rest

private def assouadSnowflakeEmbeddingFromEventFlow :
    EventFlow → Option AssouadSnowflakeEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (AssouadSnowflakeEmbeddingUp.mk
        (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEventAtDefault 0 ef))
        (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEventAtDefault 1 ef))
        (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEventAtDefault 2 ef))
        (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEventAtDefault 3 ef))
        (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEventAtDefault 4 ef))
        (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEventAtDefault 5 ef))
        (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEventAtDefault 6 ef))
        (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEventAtDefault 7 ef))
        (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEventAtDefault 8 ef))
        (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEventAtDefault 9 ef))
        (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEventAtDefault 10 ef))
        (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEventAtDefault 11 ef)))

private theorem AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AssouadSnowflakeEmbeddingUp,
      assouadSnowflakeEmbeddingFromEventFlow (assouadSnowflakeEmbeddingToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D A S E B Q R H C P N =>
      change
        some
          (AssouadSnowflakeEmbeddingUp.mk
            (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEncodeBHist M))
            (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEncodeBHist D))
            (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEncodeBHist A))
            (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEncodeBHist S))
            (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEncodeBHist E))
            (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEncodeBHist B))
            (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEncodeBHist Q))
            (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEncodeBHist R))
            (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEncodeBHist H))
            (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEncodeBHist C))
            (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEncodeBHist P))
            (assouadSnowflakeEmbeddingDecodeBHist (assouadSnowflakeEmbeddingEncodeBHist N))) =
          some (AssouadSnowflakeEmbeddingUp.mk M D A S E B Q R H C P N)
      rw [AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_decode M,
        AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_decode D,
        AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_decode A,
        AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_decode S,
        AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_decode E,
        AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_decode B,
        AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_decode Q,
        AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_decode R,
        AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_decode H,
        AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_decode C,
        AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_decode P,
        AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_decode N]

private theorem AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AssouadSnowflakeEmbeddingUp} :
    assouadSnowflakeEmbeddingToEventFlow x = assouadSnowflakeEmbeddingToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have optionEq : some x = some y := by
    calc
      some x =
          assouadSnowflakeEmbeddingFromEventFlow (assouadSnowflakeEmbeddingToEventFlow x) :=
        (AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          assouadSnowflakeEmbeddingFromEventFlow (assouadSnowflakeEmbeddingToEventFlow y) :=
        congrArg assouadSnowflakeEmbeddingFromEventFlow heq
      _ = some y := AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_fields :
    ∀ x y : AssouadSnowflakeEmbeddingUp,
      assouadSnowflakeEmbeddingFields x = assouadSnowflakeEmbeddingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ D₁ A₁ S₁ E₁ B₁ Q₁ R₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ D₂ A₂ S₂ E₂ B₂ Q₂ R₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hM tail0
          injection tail0 with hD tail1
          injection tail1 with hA tail2
          injection tail2 with hS tail3
          injection tail3 with hE tail4
          injection tail4 with hB tail5
          injection tail5 with hQ tail6
          injection tail6 with hR tail7
          injection tail7 with hH tail8
          injection tail8 with hC tail9
          injection tail9 with hP tail10
          injection tail10 with hN _
          subst hM
          subst hD
          subst hA
          subst hS
          subst hE
          subst hB
          subst hQ
          subst hR
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance assouadSnowflakeEmbeddingBHistCarrier :
    BHistCarrier AssouadSnowflakeEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := assouadSnowflakeEmbeddingToEventFlow
  fromEventFlow := assouadSnowflakeEmbeddingFromEventFlow

instance assouadSnowflakeEmbeddingChapterTasteGate :
    ChapterTasteGate AssouadSnowflakeEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      assouadSnowflakeEmbeddingFromEventFlow (assouadSnowflakeEmbeddingToEventFlow x) =
        some x
    exact AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance assouadSnowflakeEmbeddingFieldFaithful :
    FieldFaithful AssouadSnowflakeEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := assouadSnowflakeEmbeddingFields
  field_faithful := AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment_fields

instance assouadSnowflakeEmbeddingNontrivial :
    Nontrivial AssouadSnowflakeEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AssouadSnowflakeEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      AssouadSnowflakeEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AssouadSnowflakeEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  assouadSnowflakeEmbeddingChapterTasteGate

theorem AssouadSnowflakeEmbeddingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AssouadSnowflakeEmbeddingUp) ∧
      Nonempty (FieldFaithful AssouadSnowflakeEmbeddingUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial AssouadSnowflakeEmbeddingUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨assouadSnowflakeEmbeddingChapterTasteGate⟩,
      ⟨assouadSnowflakeEmbeddingFieldFaithful⟩,
      ⟨assouadSnowflakeEmbeddingNontrivial⟩⟩

end BEDC.Derived.AssouadSnowflakeEmbeddingUp
