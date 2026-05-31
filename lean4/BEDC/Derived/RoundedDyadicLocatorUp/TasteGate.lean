import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RoundedDyadicLocatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RoundedDyadicLocatorUp : Type where
  | mk (X Q S R D L U H C P N : BHist) : RoundedDyadicLocatorUp
  deriving DecidableEq

def roundedDyadicLocatorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: roundedDyadicLocatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: roundedDyadicLocatorEncodeBHist h

def roundedDyadicLocatorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (roundedDyadicLocatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (roundedDyadicLocatorDecodeBHist tail)

private theorem RoundedDyadicLocatorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, roundedDyadicLocatorDecodeBHist (roundedDyadicLocatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def roundedDyadicLocatorFields : RoundedDyadicLocatorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RoundedDyadicLocatorUp.mk X Q S R D L U H C P N => [X, Q, S, R, D, L, U, H, C, P, N]

def roundedDyadicLocatorToEventFlow : RoundedDyadicLocatorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (roundedDyadicLocatorFields x).map roundedDyadicLocatorEncodeBHist

private def RoundedDyadicLocatorTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RoundedDyadicLocatorTasteGate_single_carrier_alignment_eventAt index rest

def roundedDyadicLocatorFromEventFlow (ef : EventFlow) : Option RoundedDyadicLocatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RoundedDyadicLocatorUp.mk
      (roundedDyadicLocatorDecodeBHist
        (RoundedDyadicLocatorTasteGate_single_carrier_alignment_eventAt 0 ef))
      (roundedDyadicLocatorDecodeBHist
        (RoundedDyadicLocatorTasteGate_single_carrier_alignment_eventAt 1 ef))
      (roundedDyadicLocatorDecodeBHist
        (RoundedDyadicLocatorTasteGate_single_carrier_alignment_eventAt 2 ef))
      (roundedDyadicLocatorDecodeBHist
        (RoundedDyadicLocatorTasteGate_single_carrier_alignment_eventAt 3 ef))
      (roundedDyadicLocatorDecodeBHist
        (RoundedDyadicLocatorTasteGate_single_carrier_alignment_eventAt 4 ef))
      (roundedDyadicLocatorDecodeBHist
        (RoundedDyadicLocatorTasteGate_single_carrier_alignment_eventAt 5 ef))
      (roundedDyadicLocatorDecodeBHist
        (RoundedDyadicLocatorTasteGate_single_carrier_alignment_eventAt 6 ef))
      (roundedDyadicLocatorDecodeBHist
        (RoundedDyadicLocatorTasteGate_single_carrier_alignment_eventAt 7 ef))
      (roundedDyadicLocatorDecodeBHist
        (RoundedDyadicLocatorTasteGate_single_carrier_alignment_eventAt 8 ef))
      (roundedDyadicLocatorDecodeBHist
        (RoundedDyadicLocatorTasteGate_single_carrier_alignment_eventAt 9 ef))
      (roundedDyadicLocatorDecodeBHist
        (RoundedDyadicLocatorTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem RoundedDyadicLocatorTasteGate_single_carrier_alignment_round_trip
    (x : RoundedDyadicLocatorUp) :
    roundedDyadicLocatorFromEventFlow (roundedDyadicLocatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Q S R D L U H C P N =>
      change
        some
          (RoundedDyadicLocatorUp.mk
            (roundedDyadicLocatorDecodeBHist (roundedDyadicLocatorEncodeBHist X))
            (roundedDyadicLocatorDecodeBHist (roundedDyadicLocatorEncodeBHist Q))
            (roundedDyadicLocatorDecodeBHist (roundedDyadicLocatorEncodeBHist S))
            (roundedDyadicLocatorDecodeBHist (roundedDyadicLocatorEncodeBHist R))
            (roundedDyadicLocatorDecodeBHist (roundedDyadicLocatorEncodeBHist D))
            (roundedDyadicLocatorDecodeBHist (roundedDyadicLocatorEncodeBHist L))
            (roundedDyadicLocatorDecodeBHist (roundedDyadicLocatorEncodeBHist U))
            (roundedDyadicLocatorDecodeBHist (roundedDyadicLocatorEncodeBHist H))
            (roundedDyadicLocatorDecodeBHist (roundedDyadicLocatorEncodeBHist C))
            (roundedDyadicLocatorDecodeBHist (roundedDyadicLocatorEncodeBHist P))
            (roundedDyadicLocatorDecodeBHist (roundedDyadicLocatorEncodeBHist N))) =
          some (RoundedDyadicLocatorUp.mk X Q S R D L U H C P N)
      rw [RoundedDyadicLocatorTasteGate_single_carrier_alignment_decode_encode X,
        RoundedDyadicLocatorTasteGate_single_carrier_alignment_decode_encode Q,
        RoundedDyadicLocatorTasteGate_single_carrier_alignment_decode_encode S,
        RoundedDyadicLocatorTasteGate_single_carrier_alignment_decode_encode R,
        RoundedDyadicLocatorTasteGate_single_carrier_alignment_decode_encode D,
        RoundedDyadicLocatorTasteGate_single_carrier_alignment_decode_encode L,
        RoundedDyadicLocatorTasteGate_single_carrier_alignment_decode_encode U,
        RoundedDyadicLocatorTasteGate_single_carrier_alignment_decode_encode H,
        RoundedDyadicLocatorTasteGate_single_carrier_alignment_decode_encode C,
        RoundedDyadicLocatorTasteGate_single_carrier_alignment_decode_encode P,
        RoundedDyadicLocatorTasteGate_single_carrier_alignment_decode_encode N]

private theorem RoundedDyadicLocatorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RoundedDyadicLocatorUp} :
    roundedDyadicLocatorToEventFlow x = roundedDyadicLocatorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      roundedDyadicLocatorFromEventFlow (roundedDyadicLocatorToEventFlow x) =
        roundedDyadicLocatorFromEventFlow (roundedDyadicLocatorToEventFlow y) :=
    congrArg roundedDyadicLocatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RoundedDyadicLocatorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RoundedDyadicLocatorTasteGate_single_carrier_alignment_round_trip y)))

private theorem RoundedDyadicLocatorTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RoundedDyadicLocatorUp, roundedDyadicLocatorFields x = roundedDyadicLocatorFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X₁ Q₁ S₁ R₁ D₁ L₁ U₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk X₂ Q₂ S₂ R₂ D₂ L₂ U₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance roundedDyadicLocatorBHistCarrier : BHistCarrier RoundedDyadicLocatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := roundedDyadicLocatorToEventFlow
  fromEventFlow := roundedDyadicLocatorFromEventFlow

instance roundedDyadicLocatorChapterTasteGate : ChapterTasteGate RoundedDyadicLocatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change roundedDyadicLocatorFromEventFlow (roundedDyadicLocatorToEventFlow x) = some x
    exact RoundedDyadicLocatorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RoundedDyadicLocatorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance roundedDyadicLocatorFieldFaithful : FieldFaithful RoundedDyadicLocatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := roundedDyadicLocatorFields
  field_faithful := RoundedDyadicLocatorTasteGate_single_carrier_alignment_fields_faithful

instance roundedDyadicLocatorNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RoundedDyadicLocatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RoundedDyadicLocatorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RoundedDyadicLocatorUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RoundedDyadicLocatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  roundedDyadicLocatorChapterTasteGate

theorem RoundedDyadicLocatorTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RoundedDyadicLocatorUp) ∧
      Nonempty (FieldFaithful RoundedDyadicLocatorUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RoundedDyadicLocatorUp) ∧
          (∀ h : BHist,
            roundedDyadicLocatorDecodeBHist (roundedDyadicLocatorEncodeBHist h) = h) ∧
            (∀ x : RoundedDyadicLocatorUp,
              roundedDyadicLocatorFromEventFlow (roundedDyadicLocatorToEventFlow x) = some x) ∧
              (∀ x y : RoundedDyadicLocatorUp,
                roundedDyadicLocatorToEventFlow x = roundedDyadicLocatorToEventFlow y → x = y) ∧
                roundedDyadicLocatorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨roundedDyadicLocatorChapterTasteGate⟩,
      ⟨roundedDyadicLocatorFieldFaithful⟩,
      ⟨roundedDyadicLocatorNontrivial⟩,
      RoundedDyadicLocatorTasteGate_single_carrier_alignment_decode_encode,
      RoundedDyadicLocatorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RoundedDyadicLocatorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RoundedDyadicLocatorUp
