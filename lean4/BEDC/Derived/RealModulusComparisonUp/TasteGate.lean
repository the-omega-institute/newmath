import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealModulusComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealModulusComparisonUp : Type where
  | mk (C M0 M1 S R D E H T P N : BHist) : RealModulusComparisonUp

def realModulusComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realModulusComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realModulusComparisonEncodeBHist h

def realModulusComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realModulusComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realModulusComparisonDecodeBHist tail)

private theorem realModulusComparison_decode_encode_bhist :
    ∀ h : BHist,
      realModulusComparisonDecodeBHist (realModulusComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realModulusComparisonToEventFlow : RealModulusComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealModulusComparisonUp.mk C M0 M1 S R D E H T P N =>
      [[BMark.b0],
        realModulusComparisonEncodeBHist C,
        [BMark.b1, BMark.b0],
        realModulusComparisonEncodeBHist M0,
        [BMark.b1, BMark.b1, BMark.b0],
        realModulusComparisonEncodeBHist M1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realModulusComparisonEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realModulusComparisonEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realModulusComparisonEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realModulusComparisonEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realModulusComparisonEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realModulusComparisonEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realModulusComparisonEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realModulusComparisonEncodeBHist N]

private def realModulusComparisonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realModulusComparisonEventAtDefault index rest

def realModulusComparisonFromEventFlow
    (ef : EventFlow) : Option RealModulusComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealModulusComparisonUp.mk
      (realModulusComparisonDecodeBHist (realModulusComparisonEventAtDefault 1 ef))
      (realModulusComparisonDecodeBHist (realModulusComparisonEventAtDefault 3 ef))
      (realModulusComparisonDecodeBHist (realModulusComparisonEventAtDefault 5 ef))
      (realModulusComparisonDecodeBHist (realModulusComparisonEventAtDefault 7 ef))
      (realModulusComparisonDecodeBHist (realModulusComparisonEventAtDefault 9 ef))
      (realModulusComparisonDecodeBHist (realModulusComparisonEventAtDefault 11 ef))
      (realModulusComparisonDecodeBHist (realModulusComparisonEventAtDefault 13 ef))
      (realModulusComparisonDecodeBHist (realModulusComparisonEventAtDefault 15 ef))
      (realModulusComparisonDecodeBHist (realModulusComparisonEventAtDefault 17 ef))
      (realModulusComparisonDecodeBHist (realModulusComparisonEventAtDefault 19 ef))
      (realModulusComparisonDecodeBHist (realModulusComparisonEventAtDefault 21 ef)))

private theorem realModulusComparison_round_trip (x : RealModulusComparisonUp) :
    realModulusComparisonFromEventFlow (realModulusComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk C M0 M1 S R D E H T P N =>
      change
        some
          (RealModulusComparisonUp.mk
            (realModulusComparisonDecodeBHist (realModulusComparisonEncodeBHist C))
            (realModulusComparisonDecodeBHist (realModulusComparisonEncodeBHist M0))
            (realModulusComparisonDecodeBHist (realModulusComparisonEncodeBHist M1))
            (realModulusComparisonDecodeBHist (realModulusComparisonEncodeBHist S))
            (realModulusComparisonDecodeBHist (realModulusComparisonEncodeBHist R))
            (realModulusComparisonDecodeBHist (realModulusComparisonEncodeBHist D))
            (realModulusComparisonDecodeBHist (realModulusComparisonEncodeBHist E))
            (realModulusComparisonDecodeBHist (realModulusComparisonEncodeBHist H))
            (realModulusComparisonDecodeBHist (realModulusComparisonEncodeBHist T))
            (realModulusComparisonDecodeBHist (realModulusComparisonEncodeBHist P))
            (realModulusComparisonDecodeBHist (realModulusComparisonEncodeBHist N))) =
          some (RealModulusComparisonUp.mk C M0 M1 S R D E H T P N)
      rw [realModulusComparison_decode_encode_bhist C,
        realModulusComparison_decode_encode_bhist M0,
        realModulusComparison_decode_encode_bhist M1,
        realModulusComparison_decode_encode_bhist S,
        realModulusComparison_decode_encode_bhist R,
        realModulusComparison_decode_encode_bhist D,
        realModulusComparison_decode_encode_bhist E,
        realModulusComparison_decode_encode_bhist H,
        realModulusComparison_decode_encode_bhist T,
        realModulusComparison_decode_encode_bhist P,
        realModulusComparison_decode_encode_bhist N]

private theorem realModulusComparisonToEventFlow_injective {x y : RealModulusComparisonUp} :
    realModulusComparisonToEventFlow x = realModulusComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realModulusComparisonFromEventFlow (realModulusComparisonToEventFlow x) =
        realModulusComparisonFromEventFlow (realModulusComparisonToEventFlow y) :=
    congrArg realModulusComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realModulusComparison_round_trip x).symm
      (Eq.trans hread (realModulusComparison_round_trip y)))

private def realModulusComparisonFields : RealModulusComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealModulusComparisonUp.mk C M0 M1 S R D E H T P N => [C, M0, M1, S, R, D, E, H, T, P, N]

private theorem realModulusComparison_field_faithful :
    ∀ x y : RealModulusComparisonUp,
      realModulusComparisonFields x = realModulusComparisonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk C₁ M0₁ M1₁ S₁ R₁ D₁ E₁ H₁ T₁ P₁ N₁ =>
      cases y with
      | mk C₂ M0₂ M1₂ S₂ R₂ D₂ E₂ H₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance realModulusComparisonBHistCarrier : BHistCarrier RealModulusComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realModulusComparisonToEventFlow
  fromEventFlow := realModulusComparisonFromEventFlow

instance realModulusComparisonChapterTasteGate :
    ChapterTasteGate RealModulusComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realModulusComparisonFromEventFlow (realModulusComparisonToEventFlow x) = some x
    exact realModulusComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realModulusComparisonToEventFlow_injective heq)

instance realModulusComparisonFieldFaithful : FieldFaithful RealModulusComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realModulusComparisonFields
  field_faithful := realModulusComparison_field_faithful

instance realModulusComparisonNontrivial : Nontrivial RealModulusComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealModulusComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RealModulusComparisonUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealModulusComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realModulusComparisonChapterTasteGate

theorem RealModulusComparisonTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealModulusComparisonUp) ∧
      Nonempty (FieldFaithful RealModulusComparisonUp) ∧
        Nonempty (Nontrivial RealModulusComparisonUp) ∧
          (∀ h : BHist,
            realModulusComparisonDecodeBHist (realModulusComparisonEncodeBHist h) = h) ∧
            realModulusComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  exact
    ⟨⟨realModulusComparisonChapterTasteGate⟩,
      ⟨realModulusComparisonFieldFaithful⟩,
      ⟨realModulusComparisonNontrivial⟩,
      realModulusComparison_decode_encode_bhist,
      rfl⟩

end BEDC.Derived.RealModulusComparisonUp
