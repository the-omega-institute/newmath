import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalBestApproximationUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalBestApproximationUp : Type where
  | mk (E S G D Q L F A M T H C P N : BHist) : RationalBestApproximationUp
  deriving DecidableEq

def rationalBestApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalBestApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalBestApproximationEncodeBHist h

def rationalBestApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalBestApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalBestApproximationDecodeBHist tail)

private theorem RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalBestApproximationFields : RationalBestApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalBestApproximationUp.mk E S G D Q L F A M T H C P N =>
      [E, S, G, D, Q, L, F, A, M, T, H, C, P, N]

def rationalBestApproximationToEventFlow : RationalBestApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rationalBestApproximationFields x).map rationalBestApproximationEncodeBHist

private def rationalBestApproximationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rationalBestApproximationEventAt index rest

def rationalBestApproximationFromEventFlow (ef : EventFlow) :
    Option RationalBestApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RationalBestApproximationUp.mk
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 0 ef))
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 1 ef))
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 2 ef))
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 3 ef))
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 4 ef))
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 5 ef))
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 6 ef))
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 7 ef))
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 8 ef))
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 9 ef))
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 10 ef))
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 11 ef))
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 12 ef))
      (rationalBestApproximationDecodeBHist (rationalBestApproximationEventAt 13 ef)))

private theorem RationalBestApproximationTasteGate_single_carrier_alignment_round_trip
    (x : RationalBestApproximationUp) :
    rationalBestApproximationFromEventFlow (rationalBestApproximationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk E S G D Q L F A M T H C P N =>
      change
        some
          (RationalBestApproximationUp.mk
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist E))
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist S))
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist G))
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist D))
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist Q))
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist L))
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist F))
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist A))
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist M))
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist T))
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist H))
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist C))
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist P))
            (rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist N))) =
          some (RationalBestApproximationUp.mk E S G D Q L F A M T H C P N)
      rw [RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode E,
        RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode S,
        RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode G,
        RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode D,
        RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode Q,
        RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode L,
        RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode F,
        RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode A,
        RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode M,
        RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode T,
        RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode H,
        RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode C,
        RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode P,
        RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode N]

private theorem RationalBestApproximationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RationalBestApproximationUp} :
    rationalBestApproximationToEventFlow x = rationalBestApproximationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalBestApproximationFromEventFlow (rationalBestApproximationToEventFlow x) =
        rationalBestApproximationFromEventFlow (rationalBestApproximationToEventFlow y) :=
    congrArg rationalBestApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RationalBestApproximationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RationalBestApproximationTasteGate_single_carrier_alignment_round_trip y)))

private theorem RationalBestApproximationTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RationalBestApproximationUp,
      rationalBestApproximationFields x = rationalBestApproximationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E₁ S₁ G₁ D₁ Q₁ L₁ F₁ A₁ M₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk E₂ S₂ G₂ D₂ Q₂ L₂ F₂ A₂ M₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance rationalBestApproximationBHistCarrier :
    BHistCarrier RationalBestApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalBestApproximationToEventFlow
  fromEventFlow := rationalBestApproximationFromEventFlow

instance rationalBestApproximationChapterTasteGate :
    ChapterTasteGate RationalBestApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      rationalBestApproximationFromEventFlow (rationalBestApproximationToEventFlow x) =
        some x
    exact RationalBestApproximationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RationalBestApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance rationalBestApproximationFieldFaithful :
    FieldFaithful RationalBestApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rationalBestApproximationFields
  field_faithful := RationalBestApproximationTasteGate_single_carrier_alignment_fields_faithful

instance rationalBestApproximationNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RationalBestApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RationalBestApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RationalBestApproximationUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RationalBestApproximationTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RationalBestApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalBestApproximationChapterTasteGate

theorem RationalBestApproximationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RationalBestApproximationUp) ∧
      Nonempty (FieldFaithful RationalBestApproximationUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RationalBestApproximationUp) ∧
          (∀ h : BHist,
            rationalBestApproximationDecodeBHist (rationalBestApproximationEncodeBHist h) =
              h) ∧
            (∀ x : RationalBestApproximationUp,
              rationalBestApproximationFromEventFlow
                  (rationalBestApproximationToEventFlow x) =
                some x) ∧
              (∀ x y : RationalBestApproximationUp,
                rationalBestApproximationToEventFlow x =
                    rationalBestApproximationToEventFlow y →
                  x = y) ∧
                rationalBestApproximationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨rationalBestApproximationChapterTasteGate⟩,
      ⟨rationalBestApproximationFieldFaithful⟩,
      ⟨rationalBestApproximationNontrivial⟩,
      RationalBestApproximationTasteGate_single_carrier_alignment_decode_encode,
      RationalBestApproximationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RationalBestApproximationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RationalBestApproximationUp.TasteGate
