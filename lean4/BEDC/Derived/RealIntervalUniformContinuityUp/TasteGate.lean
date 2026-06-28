import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealIntervalUniformContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealIntervalUniformContinuityUp : Type where
  | mk (I L F T W R D M E H C P N : BHist) : RealIntervalUniformContinuityUp
  deriving DecidableEq

def realIntervalUniformContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realIntervalUniformContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realIntervalUniformContinuityEncodeBHist h

def realIntervalUniformContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realIntervalUniformContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realIntervalUniformContinuityDecodeBHist tail)

private theorem RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realIntervalUniformContinuityFields :
    RealIntervalUniformContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealIntervalUniformContinuityUp.mk I L F T W R D M E H C P N =>
      [I, L, F, T, W, R, D, M, E, H, C, P, N]

def realIntervalUniformContinuityToEventFlow :
    RealIntervalUniformContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (realIntervalUniformContinuityFields x).map
        realIntervalUniformContinuityEncodeBHist

private def realIntervalUniformContinuityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realIntervalUniformContinuityEventAt index rest

def realIntervalUniformContinuityFromEventFlow
    (ef : EventFlow) : Option RealIntervalUniformContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealIntervalUniformContinuityUp.mk
      (realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEventAt 0 ef))
      (realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEventAt 1 ef))
      (realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEventAt 2 ef))
      (realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEventAt 3 ef))
      (realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEventAt 4 ef))
      (realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEventAt 5 ef))
      (realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEventAt 6 ef))
      (realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEventAt 7 ef))
      (realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEventAt 8 ef))
      (realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEventAt 9 ef))
      (realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEventAt 10 ef))
      (realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEventAt 11 ef))
      (realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEventAt 12 ef)))

private theorem RealIntervalUniformContinuityTasteGate_single_carrier_alignment_round_trip
    (x : RealIntervalUniformContinuityUp) :
    realIntervalUniformContinuityFromEventFlow
      (realIntervalUniformContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I L F T W R D M E H C P N =>
      change
        some
          (RealIntervalUniformContinuityUp.mk
            (realIntervalUniformContinuityDecodeBHist
              (realIntervalUniformContinuityEncodeBHist I))
            (realIntervalUniformContinuityDecodeBHist
              (realIntervalUniformContinuityEncodeBHist L))
            (realIntervalUniformContinuityDecodeBHist
              (realIntervalUniformContinuityEncodeBHist F))
            (realIntervalUniformContinuityDecodeBHist
              (realIntervalUniformContinuityEncodeBHist T))
            (realIntervalUniformContinuityDecodeBHist
              (realIntervalUniformContinuityEncodeBHist W))
            (realIntervalUniformContinuityDecodeBHist
              (realIntervalUniformContinuityEncodeBHist R))
            (realIntervalUniformContinuityDecodeBHist
              (realIntervalUniformContinuityEncodeBHist D))
            (realIntervalUniformContinuityDecodeBHist
              (realIntervalUniformContinuityEncodeBHist M))
            (realIntervalUniformContinuityDecodeBHist
              (realIntervalUniformContinuityEncodeBHist E))
            (realIntervalUniformContinuityDecodeBHist
              (realIntervalUniformContinuityEncodeBHist H))
            (realIntervalUniformContinuityDecodeBHist
              (realIntervalUniformContinuityEncodeBHist C))
            (realIntervalUniformContinuityDecodeBHist
              (realIntervalUniformContinuityEncodeBHist P))
            (realIntervalUniformContinuityDecodeBHist
              (realIntervalUniformContinuityEncodeBHist N))) =
          some (RealIntervalUniformContinuityUp.mk I L F T W R D M E H C P N)
      rw [RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode I,
        RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode L,
        RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode F,
        RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode T,
        RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode W,
        RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode R,
        RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode D,
        RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode M,
        RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode E,
        RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode H,
        RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode C,
        RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode P,
        RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealIntervalUniformContinuityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealIntervalUniformContinuityUp} :
    realIntervalUniformContinuityToEventFlow x =
      realIntervalUniformContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realIntervalUniformContinuityFromEventFlow
          (realIntervalUniformContinuityToEventFlow x) =
        realIntervalUniformContinuityFromEventFlow
          (realIntervalUniformContinuityToEventFlow y) :=
    congrArg realIntervalUniformContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealIntervalUniformContinuityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealIntervalUniformContinuityTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealIntervalUniformContinuityTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealIntervalUniformContinuityUp,
      realIntervalUniformContinuityFields x =
        realIntervalUniformContinuityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I₁ L₁ F₁ T₁ W₁ R₁ D₁ M₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk I₂ L₂ F₂ T₂ W₂ R₂ D₂ M₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance realIntervalUniformContinuityBHistCarrier :
    BHistCarrier RealIntervalUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realIntervalUniformContinuityToEventFlow
  fromEventFlow := realIntervalUniformContinuityFromEventFlow

instance realIntervalUniformContinuityChapterTasteGate :
    ChapterTasteGate RealIntervalUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realIntervalUniformContinuityFromEventFlow
        (realIntervalUniformContinuityToEventFlow x) = some x
    exact RealIntervalUniformContinuityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RealIntervalUniformContinuityTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance realIntervalUniformContinuityFieldFaithful :
    FieldFaithful RealIntervalUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realIntervalUniformContinuityFields
  field_faithful := RealIntervalUniformContinuityTasteGate_single_carrier_alignment_fields

instance realIntervalUniformContinuityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RealIntervalUniformContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealIntervalUniformContinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RealIntervalUniformContinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RealIntervalUniformContinuityTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RealIntervalUniformContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realIntervalUniformContinuityChapterTasteGate

theorem RealIntervalUniformContinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realIntervalUniformContinuityDecodeBHist
        (realIntervalUniformContinuityEncodeBHist h) = h) ∧
      (∀ x : RealIntervalUniformContinuityUp,
        realIntervalUniformContinuityFromEventFlow
          (realIntervalUniformContinuityToEventFlow x) = some x) ∧
        (∀ x y : RealIntervalUniformContinuityUp,
          realIntervalUniformContinuityToEventFlow x =
            realIntervalUniformContinuityToEventFlow y → x = y) ∧
          realIntervalUniformContinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact RealIntervalUniformContinuityTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact RealIntervalUniformContinuityTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact RealIntervalUniformContinuityTasteGate_single_carrier_alignment_toEventFlow_injective
      heq
  · rfl

end BEDC.Derived.RealIntervalUniformContinuityUp
