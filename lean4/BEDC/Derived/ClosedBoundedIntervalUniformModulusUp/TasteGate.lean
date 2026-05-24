import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClosedBoundedIntervalUniformModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClosedBoundedIntervalUniformModulusUp : Type where
  | mk
      (leftEndpoint rightEndpoint intervalRow compactCover dyadicCover lebesgueLedger
        pointwiseModulus uniformOutput transport route provenance name : BHist) :
      ClosedBoundedIntervalUniformModulusUp
  deriving DecidableEq

def closedBoundedIntervalUniformModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: closedBoundedIntervalUniformModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: closedBoundedIntervalUniformModulusEncodeBHist h

def closedBoundedIntervalUniformModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (closedBoundedIntervalUniformModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (closedBoundedIntervalUniformModulusDecodeBHist tail)

private theorem closedBoundedIntervalUniformModulus_decode_encode_bhist :
    ∀ h : BHist,
      closedBoundedIntervalUniformModulusDecodeBHist
          (closedBoundedIntervalUniformModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def closedBoundedIntervalUniformModulusFields :
    ClosedBoundedIntervalUniformModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClosedBoundedIntervalUniformModulusUp.mk leftEndpoint rightEndpoint intervalRow
      compactCover dyadicCover lebesgueLedger pointwiseModulus uniformOutput transport route
      provenance name =>
      [leftEndpoint, rightEndpoint, intervalRow, compactCover, dyadicCover, lebesgueLedger,
        pointwiseModulus, uniformOutput, transport, route, provenance, name]

def closedBoundedIntervalUniformModulusToEventFlow :
    ClosedBoundedIntervalUniformModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (closedBoundedIntervalUniformModulusFields x).map
        closedBoundedIntervalUniformModulusEncodeBHist

private def closedBoundedIntervalUniformModulusEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      closedBoundedIntervalUniformModulusEventAtDefault index rest

def closedBoundedIntervalUniformModulusFromEventFlow
    (ef : EventFlow) : Option ClosedBoundedIntervalUniformModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClosedBoundedIntervalUniformModulusUp.mk
      (closedBoundedIntervalUniformModulusDecodeBHist
        (closedBoundedIntervalUniformModulusEventAtDefault 0 ef))
      (closedBoundedIntervalUniformModulusDecodeBHist
        (closedBoundedIntervalUniformModulusEventAtDefault 1 ef))
      (closedBoundedIntervalUniformModulusDecodeBHist
        (closedBoundedIntervalUniformModulusEventAtDefault 2 ef))
      (closedBoundedIntervalUniformModulusDecodeBHist
        (closedBoundedIntervalUniformModulusEventAtDefault 3 ef))
      (closedBoundedIntervalUniformModulusDecodeBHist
        (closedBoundedIntervalUniformModulusEventAtDefault 4 ef))
      (closedBoundedIntervalUniformModulusDecodeBHist
        (closedBoundedIntervalUniformModulusEventAtDefault 5 ef))
      (closedBoundedIntervalUniformModulusDecodeBHist
        (closedBoundedIntervalUniformModulusEventAtDefault 6 ef))
      (closedBoundedIntervalUniformModulusDecodeBHist
        (closedBoundedIntervalUniformModulusEventAtDefault 7 ef))
      (closedBoundedIntervalUniformModulusDecodeBHist
        (closedBoundedIntervalUniformModulusEventAtDefault 8 ef))
      (closedBoundedIntervalUniformModulusDecodeBHist
        (closedBoundedIntervalUniformModulusEventAtDefault 9 ef))
      (closedBoundedIntervalUniformModulusDecodeBHist
        (closedBoundedIntervalUniformModulusEventAtDefault 10 ef))
      (closedBoundedIntervalUniformModulusDecodeBHist
        (closedBoundedIntervalUniformModulusEventAtDefault 11 ef)))

private theorem closedBoundedIntervalUniformModulus_round_trip :
    ∀ x : ClosedBoundedIntervalUniformModulusUp,
      closedBoundedIntervalUniformModulusFromEventFlow
          (closedBoundedIntervalUniformModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk leftEndpoint rightEndpoint intervalRow compactCover dyadicCover lebesgueLedger
      pointwiseModulus uniformOutput transport route provenance name =>
      change
        some
          (ClosedBoundedIntervalUniformModulusUp.mk
            (closedBoundedIntervalUniformModulusDecodeBHist
              (closedBoundedIntervalUniformModulusEncodeBHist leftEndpoint))
            (closedBoundedIntervalUniformModulusDecodeBHist
              (closedBoundedIntervalUniformModulusEncodeBHist rightEndpoint))
            (closedBoundedIntervalUniformModulusDecodeBHist
              (closedBoundedIntervalUniformModulusEncodeBHist intervalRow))
            (closedBoundedIntervalUniformModulusDecodeBHist
              (closedBoundedIntervalUniformModulusEncodeBHist compactCover))
            (closedBoundedIntervalUniformModulusDecodeBHist
              (closedBoundedIntervalUniformModulusEncodeBHist dyadicCover))
            (closedBoundedIntervalUniformModulusDecodeBHist
              (closedBoundedIntervalUniformModulusEncodeBHist lebesgueLedger))
            (closedBoundedIntervalUniformModulusDecodeBHist
              (closedBoundedIntervalUniformModulusEncodeBHist pointwiseModulus))
            (closedBoundedIntervalUniformModulusDecodeBHist
              (closedBoundedIntervalUniformModulusEncodeBHist uniformOutput))
            (closedBoundedIntervalUniformModulusDecodeBHist
              (closedBoundedIntervalUniformModulusEncodeBHist transport))
            (closedBoundedIntervalUniformModulusDecodeBHist
              (closedBoundedIntervalUniformModulusEncodeBHist route))
            (closedBoundedIntervalUniformModulusDecodeBHist
              (closedBoundedIntervalUniformModulusEncodeBHist provenance))
            (closedBoundedIntervalUniformModulusDecodeBHist
              (closedBoundedIntervalUniformModulusEncodeBHist name))) =
          some
            (ClosedBoundedIntervalUniformModulusUp.mk leftEndpoint rightEndpoint intervalRow
              compactCover dyadicCover lebesgueLedger pointwiseModulus uniformOutput transport
              route provenance name)
      rw [closedBoundedIntervalUniformModulus_decode_encode_bhist leftEndpoint,
        closedBoundedIntervalUniformModulus_decode_encode_bhist rightEndpoint,
        closedBoundedIntervalUniformModulus_decode_encode_bhist intervalRow,
        closedBoundedIntervalUniformModulus_decode_encode_bhist compactCover,
        closedBoundedIntervalUniformModulus_decode_encode_bhist dyadicCover,
        closedBoundedIntervalUniformModulus_decode_encode_bhist lebesgueLedger,
        closedBoundedIntervalUniformModulus_decode_encode_bhist pointwiseModulus,
        closedBoundedIntervalUniformModulus_decode_encode_bhist uniformOutput,
        closedBoundedIntervalUniformModulus_decode_encode_bhist transport,
        closedBoundedIntervalUniformModulus_decode_encode_bhist route,
        closedBoundedIntervalUniformModulus_decode_encode_bhist provenance,
        closedBoundedIntervalUniformModulus_decode_encode_bhist name]

private theorem closedBoundedIntervalUniformModulusToEventFlow_injective
    {x y : ClosedBoundedIntervalUniformModulusUp} :
    closedBoundedIntervalUniformModulusToEventFlow x =
        closedBoundedIntervalUniformModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      closedBoundedIntervalUniformModulusFromEventFlow
          (closedBoundedIntervalUniformModulusToEventFlow x) =
        closedBoundedIntervalUniformModulusFromEventFlow
          (closedBoundedIntervalUniformModulusToEventFlow y) :=
    congrArg closedBoundedIntervalUniformModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (closedBoundedIntervalUniformModulus_round_trip x).symm
      (Eq.trans hread (closedBoundedIntervalUniformModulus_round_trip y)))

private theorem closedBoundedIntervalUniformModulus_fields_faithful :
    ∀ x y : ClosedBoundedIntervalUniformModulusUp,
      closedBoundedIntervalUniformModulusFields x =
          closedBoundedIntervalUniformModulusFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk l₁ r₁ i₁ c₁ d₁ g₁ p₁ u₁ h₁ q₁ v₁ n₁ =>
      cases y with
      | mk l₂ r₂ i₂ c₂ d₂ g₂ p₂ u₂ h₂ q₂ v₂ n₂ =>
          cases hfields
          rfl

instance closedBoundedIntervalUniformModulusBHistCarrier :
    BHistCarrier ClosedBoundedIntervalUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := closedBoundedIntervalUniformModulusToEventFlow
  fromEventFlow := closedBoundedIntervalUniformModulusFromEventFlow

instance closedBoundedIntervalUniformModulusChapterTasteGate :
    ChapterTasteGate ClosedBoundedIntervalUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      closedBoundedIntervalUniformModulusFromEventFlow
          (closedBoundedIntervalUniformModulusToEventFlow x) =
        some x
    exact closedBoundedIntervalUniformModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (closedBoundedIntervalUniformModulusToEventFlow_injective heq)

instance closedBoundedIntervalUniformModulusFieldFaithful :
    FieldFaithful ClosedBoundedIntervalUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := closedBoundedIntervalUniformModulusFields
  field_faithful := closedBoundedIntervalUniformModulus_fields_faithful

instance closedBoundedIntervalUniformModulusNontrivial :
    Nontrivial ClosedBoundedIntervalUniformModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClosedBoundedIntervalUniformModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ClosedBoundedIntervalUniformModulusUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ClosedBoundedIntervalUniformModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ClosedBoundedIntervalUniformModulusUp) ∧
      Nonempty (FieldFaithful ClosedBoundedIntervalUniformModulusUp) ∧
        Nonempty (Nontrivial ClosedBoundedIntervalUniformModulusUp) ∧
          (∀ h : BHist,
            closedBoundedIntervalUniformModulusDecodeBHist
                (closedBoundedIntervalUniformModulusEncodeBHist h) =
              h) ∧
            (∀ x : ClosedBoundedIntervalUniformModulusUp,
              closedBoundedIntervalUniformModulusFromEventFlow
                  (closedBoundedIntervalUniformModulusToEventFlow x) =
                some x) ∧
              closedBoundedIntervalUniformModulusEncodeBHist BHist.Empty =
                ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨⟨closedBoundedIntervalUniformModulusChapterTasteGate⟩,
      ⟨⟨closedBoundedIntervalUniformModulusFieldFaithful⟩,
        ⟨⟨closedBoundedIntervalUniformModulusNontrivial⟩,
          closedBoundedIntervalUniformModulus_decode_encode_bhist,
          closedBoundedIntervalUniformModulus_round_trip,
          rfl⟩⟩⟩

theorem ClosedBoundedIntervalUniformModulus_heine_cantor_route_rows
    (I : ClosedBoundedIntervalUniformModulusUp) :
    ∃ A B R C D L M U H Q P N : BHist,
      closedBoundedIntervalUniformModulusFields I = [A, B, R, C, D, L, M, U, H, Q, P, N] ∧
        closedBoundedIntervalUniformModulusFromEventFlow
            (([A, B, R, C, D, L, M, U, H, Q, P, N] : List BHist).map
              closedBoundedIntervalUniformModulusEncodeBHist) =
          some I ∧
          closedBoundedIntervalUniformModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases I with
  | mk A B R C D L M U H Q P N =>
      exact
        ⟨A, B, R, C, D, L, M, U, H, Q, P, N, rfl,
          closedBoundedIntervalUniformModulus_round_trip
            (ClosedBoundedIntervalUniformModulusUp.mk A B R C D L M U H Q P N),
          rfl⟩

end BEDC.Derived.ClosedBoundedIntervalUniformModulusUp
