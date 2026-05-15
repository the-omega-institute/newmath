import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChurchEliminatorRegressionMatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChurchEliminatorRegressionMatrixUp : Type where
  | mk (F G L C B S X H K P N : BHist) : ChurchEliminatorRegressionMatrixUp

def churchEliminatorRegressionMatrixEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: churchEliminatorRegressionMatrixEncodeBHist h
  | BHist.e1 h => BMark.b1 :: churchEliminatorRegressionMatrixEncodeBHist h

def churchEliminatorRegressionMatrixDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (churchEliminatorRegressionMatrixDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (churchEliminatorRegressionMatrixDecodeBHist tail)

private theorem churchEliminatorRegressionMatrix_decode_encode_bhist :
    ∀ h : BHist,
      churchEliminatorRegressionMatrixDecodeBHist
        (churchEliminatorRegressionMatrixEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def churchEliminatorRegressionMatrixToEventFlow :
    ChurchEliminatorRegressionMatrixUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ChurchEliminatorRegressionMatrixUp.mk F G L C B S X H K P N =>
      [[BMark.b0],
        churchEliminatorRegressionMatrixEncodeBHist F,
        [BMark.b1, BMark.b0],
        churchEliminatorRegressionMatrixEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b0],
        churchEliminatorRegressionMatrixEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        churchEliminatorRegressionMatrixEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        churchEliminatorRegressionMatrixEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        churchEliminatorRegressionMatrixEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        churchEliminatorRegressionMatrixEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        churchEliminatorRegressionMatrixEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        churchEliminatorRegressionMatrixEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        churchEliminatorRegressionMatrixEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        churchEliminatorRegressionMatrixEncodeBHist N]

private def churchEliminatorRegressionMatrixEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      churchEliminatorRegressionMatrixEventAtDefault index rest

def churchEliminatorRegressionMatrixFromEventFlow
    (ef : EventFlow) : Option ChurchEliminatorRegressionMatrixUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ChurchEliminatorRegressionMatrixUp.mk
      (churchEliminatorRegressionMatrixDecodeBHist
        (churchEliminatorRegressionMatrixEventAtDefault 1 ef))
      (churchEliminatorRegressionMatrixDecodeBHist
        (churchEliminatorRegressionMatrixEventAtDefault 3 ef))
      (churchEliminatorRegressionMatrixDecodeBHist
        (churchEliminatorRegressionMatrixEventAtDefault 5 ef))
      (churchEliminatorRegressionMatrixDecodeBHist
        (churchEliminatorRegressionMatrixEventAtDefault 7 ef))
      (churchEliminatorRegressionMatrixDecodeBHist
        (churchEliminatorRegressionMatrixEventAtDefault 9 ef))
      (churchEliminatorRegressionMatrixDecodeBHist
        (churchEliminatorRegressionMatrixEventAtDefault 11 ef))
      (churchEliminatorRegressionMatrixDecodeBHist
        (churchEliminatorRegressionMatrixEventAtDefault 13 ef))
      (churchEliminatorRegressionMatrixDecodeBHist
        (churchEliminatorRegressionMatrixEventAtDefault 15 ef))
      (churchEliminatorRegressionMatrixDecodeBHist
        (churchEliminatorRegressionMatrixEventAtDefault 17 ef))
      (churchEliminatorRegressionMatrixDecodeBHist
        (churchEliminatorRegressionMatrixEventAtDefault 19 ef))
      (churchEliminatorRegressionMatrixDecodeBHist
        (churchEliminatorRegressionMatrixEventAtDefault 21 ef)))

private theorem churchEliminatorRegressionMatrix_round_trip :
    ∀ x : ChurchEliminatorRegressionMatrixUp,
      churchEliminatorRegressionMatrixFromEventFlow
        (churchEliminatorRegressionMatrixToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F G L C B S X H K P N =>
      change
        some
          (ChurchEliminatorRegressionMatrixUp.mk
            (churchEliminatorRegressionMatrixDecodeBHist
              (churchEliminatorRegressionMatrixEncodeBHist F))
            (churchEliminatorRegressionMatrixDecodeBHist
              (churchEliminatorRegressionMatrixEncodeBHist G))
            (churchEliminatorRegressionMatrixDecodeBHist
              (churchEliminatorRegressionMatrixEncodeBHist L))
            (churchEliminatorRegressionMatrixDecodeBHist
              (churchEliminatorRegressionMatrixEncodeBHist C))
            (churchEliminatorRegressionMatrixDecodeBHist
              (churchEliminatorRegressionMatrixEncodeBHist B))
            (churchEliminatorRegressionMatrixDecodeBHist
              (churchEliminatorRegressionMatrixEncodeBHist S))
            (churchEliminatorRegressionMatrixDecodeBHist
              (churchEliminatorRegressionMatrixEncodeBHist X))
            (churchEliminatorRegressionMatrixDecodeBHist
              (churchEliminatorRegressionMatrixEncodeBHist H))
            (churchEliminatorRegressionMatrixDecodeBHist
              (churchEliminatorRegressionMatrixEncodeBHist K))
            (churchEliminatorRegressionMatrixDecodeBHist
              (churchEliminatorRegressionMatrixEncodeBHist P))
            (churchEliminatorRegressionMatrixDecodeBHist
              (churchEliminatorRegressionMatrixEncodeBHist N))) =
          some (ChurchEliminatorRegressionMatrixUp.mk F G L C B S X H K P N)
      rw [churchEliminatorRegressionMatrix_decode_encode_bhist F,
        churchEliminatorRegressionMatrix_decode_encode_bhist G,
        churchEliminatorRegressionMatrix_decode_encode_bhist L,
        churchEliminatorRegressionMatrix_decode_encode_bhist C,
        churchEliminatorRegressionMatrix_decode_encode_bhist B,
        churchEliminatorRegressionMatrix_decode_encode_bhist S,
        churchEliminatorRegressionMatrix_decode_encode_bhist X,
        churchEliminatorRegressionMatrix_decode_encode_bhist H,
        churchEliminatorRegressionMatrix_decode_encode_bhist K,
        churchEliminatorRegressionMatrix_decode_encode_bhist P,
        churchEliminatorRegressionMatrix_decode_encode_bhist N]

private theorem churchEliminatorRegressionMatrixToEventFlow_injective
    {x y : ChurchEliminatorRegressionMatrixUp} :
    churchEliminatorRegressionMatrixToEventFlow x =
      churchEliminatorRegressionMatrixToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      churchEliminatorRegressionMatrixFromEventFlow
        (churchEliminatorRegressionMatrixToEventFlow x) =
        churchEliminatorRegressionMatrixFromEventFlow
          (churchEliminatorRegressionMatrixToEventFlow y) :=
    congrArg churchEliminatorRegressionMatrixFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (churchEliminatorRegressionMatrix_round_trip x).symm
      (Eq.trans hread (churchEliminatorRegressionMatrix_round_trip y)))

private def churchEliminatorRegressionMatrixFields :
    ChurchEliminatorRegressionMatrixUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ChurchEliminatorRegressionMatrixUp.mk F G L C B S X H K P N =>
      [F, G, L, C, B, S, X, H, K, P, N]

private theorem churchEliminatorRegressionMatrix_field_faithful :
    ∀ x y : ChurchEliminatorRegressionMatrixUp,
      churchEliminatorRegressionMatrixFields x =
        churchEliminatorRegressionMatrixFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ G₁ L₁ C₁ B₁ S₁ X₁ H₁ K₁ P₁ N₁ =>
      cases y with
      | mk F₂ G₂ L₂ C₂ B₂ S₂ X₂ H₂ K₂ P₂ N₂ =>
          cases hfields
          rfl

instance churchEliminatorRegressionMatrixBHistCarrier :
    BHistCarrier ChurchEliminatorRegressionMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := churchEliminatorRegressionMatrixToEventFlow
  fromEventFlow := churchEliminatorRegressionMatrixFromEventFlow

instance churchEliminatorRegressionMatrixChapterTasteGate :
    ChapterTasteGate ChurchEliminatorRegressionMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      churchEliminatorRegressionMatrixFromEventFlow
        (churchEliminatorRegressionMatrixToEventFlow x) = some x
    exact churchEliminatorRegressionMatrix_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (churchEliminatorRegressionMatrixToEventFlow_injective heq)

instance churchEliminatorRegressionMatrixFieldFaithful :
    FieldFaithful ChurchEliminatorRegressionMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := churchEliminatorRegressionMatrixFields
  field_faithful := churchEliminatorRegressionMatrix_field_faithful

instance churchEliminatorRegressionMatrixNontrivial :
    Nontrivial ChurchEliminatorRegressionMatrixUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ChurchEliminatorRegressionMatrixUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ChurchEliminatorRegressionMatrixUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ChurchEliminatorRegressionMatrixUp :=
  -- BEDC touchpoint anchor: BHist BMark
  churchEliminatorRegressionMatrixChapterTasteGate

theorem ChurchEliminatorRegressionMatrixTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ChurchEliminatorRegressionMatrixUp) ∧
      Nonempty (FieldFaithful ChurchEliminatorRegressionMatrixUp) ∧
        Nonempty (Nontrivial ChurchEliminatorRegressionMatrixUp) ∧
          (∀ h : BHist,
            churchEliminatorRegressionMatrixDecodeBHist
              (churchEliminatorRegressionMatrixEncodeBHist h) = h) ∧
            churchEliminatorRegressionMatrixEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨churchEliminatorRegressionMatrixChapterTasteGate⟩,
      ⟨churchEliminatorRegressionMatrixFieldFaithful⟩,
      ⟨churchEliminatorRegressionMatrixNontrivial⟩,
      churchEliminatorRegressionMatrix_decode_encode_bhist,
      rfl⟩

end BEDC.Derived.ChurchEliminatorRegressionMatrixUp
