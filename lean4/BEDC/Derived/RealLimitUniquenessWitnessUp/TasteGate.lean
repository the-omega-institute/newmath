import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealLimitUniquenessWitnessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealLimitUniquenessWitnessUp : Type where
  | mk (D0 D1 Q S R0 R1 E V H C P N : BHist) : RealLimitUniquenessWitnessUp
  deriving DecidableEq

def realLimitUniquenessWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realLimitUniquenessWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realLimitUniquenessWitnessEncodeBHist h

def realLimitUniquenessWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realLimitUniquenessWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realLimitUniquenessWitnessDecodeBHist tail)

private theorem RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realLimitUniquenessWitnessFields : RealLimitUniquenessWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealLimitUniquenessWitnessUp.mk D0 D1 Q S R0 R1 E V H C P N =>
      [D0, D1, Q, S, R0, R1, E, V, H, C, P, N]

def realLimitUniquenessWitnessToEventFlow : RealLimitUniquenessWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealLimitUniquenessWitnessUp.mk D0 D1 Q S R0 R1 E V H C P N =>
      [[BMark.b0],
        realLimitUniquenessWitnessEncodeBHist D0,
        [BMark.b1, BMark.b0],
        realLimitUniquenessWitnessEncodeBHist D1,
        [BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessWitnessEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessWitnessEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessWitnessEncodeBHist R0,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessWitnessEncodeBHist R1,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessWitnessEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realLimitUniquenessWitnessEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realLimitUniquenessWitnessEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessWitnessEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessWitnessEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realLimitUniquenessWitnessEncodeBHist N]

private def realLimitUniquenessWitnessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realLimitUniquenessWitnessEventAtDefault index rest

def realLimitUniquenessWitnessFromEventFlow
    (ef : EventFlow) : Option RealLimitUniquenessWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealLimitUniquenessWitnessUp.mk
      (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEventAtDefault 1 ef))
      (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEventAtDefault 3 ef))
      (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEventAtDefault 5 ef))
      (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEventAtDefault 7 ef))
      (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEventAtDefault 9 ef))
      (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEventAtDefault 11 ef))
      (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEventAtDefault 13 ef))
      (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEventAtDefault 15 ef))
      (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEventAtDefault 17 ef))
      (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEventAtDefault 19 ef))
      (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEventAtDefault 21 ef))
      (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEventAtDefault 23 ef)))

private theorem RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealLimitUniquenessWitnessUp,
      realLimitUniquenessWitnessFromEventFlow (realLimitUniquenessWitnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D0 D1 Q S R0 R1 E V H C P N =>
      change
        some
          (RealLimitUniquenessWitnessUp.mk
            (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist D0))
            (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist D1))
            (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist Q))
            (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist S))
            (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist R0))
            (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist R1))
            (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist E))
            (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist V))
            (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist H))
            (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist C))
            (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist P))
            (realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist N))) =
          some (RealLimitUniquenessWitnessUp.mk D0 D1 Q S R0 R1 E V H C P N)
      rw [RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode D0,
        RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode D1,
        RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode Q,
        RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode S,
        RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode R0,
        RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode R1,
        RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode E,
        RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode V,
        RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode H,
        RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode C,
        RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode P,
        RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode N]

private theorem RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_injective
    {x y : RealLimitUniquenessWitnessUp} :
    realLimitUniquenessWitnessToEventFlow x = realLimitUniquenessWitnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realLimitUniquenessWitnessFromEventFlow (realLimitUniquenessWitnessToEventFlow x) =
        realLimitUniquenessWitnessFromEventFlow (realLimitUniquenessWitnessToEventFlow y) :=
    congrArg realLimitUniquenessWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_fields :
    ∀ x y : RealLimitUniquenessWitnessUp,
      realLimitUniquenessWitnessFields x = realLimitUniquenessWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D0₁ D1₁ Q₁ S₁ R0₁ R1₁ E₁ V₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk D0₂ D1₂ Q₂ S₂ R0₂ R1₂ E₂ V₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance realLimitUniquenessWitnessBHistCarrier :
    BHistCarrier RealLimitUniquenessWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realLimitUniquenessWitnessToEventFlow
  fromEventFlow := realLimitUniquenessWitnessFromEventFlow

instance realLimitUniquenessWitnessChapterTasteGate :
    ChapterTasteGate RealLimitUniquenessWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realLimitUniquenessWitnessFromEventFlow (realLimitUniquenessWitnessToEventFlow x) =
      some x
    exact RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_injective heq)

instance realLimitUniquenessWitnessFieldFaithful :
    FieldFaithful RealLimitUniquenessWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realLimitUniquenessWitnessFields
  field_faithful := RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_fields

instance realLimitUniquenessWitnessNontrivial :
    Nontrivial RealLimitUniquenessWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealLimitUniquenessWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RealLimitUniquenessWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealLimitUniquenessWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realLimitUniquenessWitnessChapterTasteGate

theorem RealLimitUniquenessWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realLimitUniquenessWitnessDecodeBHist (realLimitUniquenessWitnessEncodeBHist h) = h) ∧
      realLimitUniquenessWitnessEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x y : RealLimitUniquenessWitnessUp,
          realLimitUniquenessWitnessFields x = realLimitUniquenessWitnessFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_decode,
      rfl,
      RealLimitUniquenessWitnessTasteGate_single_carrier_alignment_fields⟩

end BEDC.Derived.RealLimitUniquenessWitnessUp.TasteGate
