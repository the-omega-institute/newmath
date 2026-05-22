import BEDC.Derived.RealUniformEmbeddingUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformEmbeddingUp

open BEDC.Derived
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def realUniformEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realUniformEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realUniformEmbeddingEncodeBHist h

def realUniformEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realUniformEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realUniformEmbeddingDecodeBHist tail)

private theorem realUniformEmbedding_decode_encode_bhist :
    ∀ h : BHist,
      realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realUniformEmbeddingFields : RealUniformEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformEmbeddingUp.mk S W D Q E U H C P N => [S, W, D, Q, E, U, H, C, P, N]

def realUniformEmbeddingToEventFlow : RealUniformEmbeddingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realUniformEmbeddingFields x).map realUniformEmbeddingEncodeBHist

private def realUniformEmbeddingRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => realUniformEmbeddingRawAt n rest

private def realUniformEmbeddingLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => realUniformEmbeddingLengthEq n rest

def realUniformEmbeddingFromEventFlow : EventFlow → Option RealUniformEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match realUniformEmbeddingLengthEq 10 flow with
      | true =>
          some
            (RealUniformEmbeddingUp.mk
              (realUniformEmbeddingDecodeBHist (realUniformEmbeddingRawAt 0 flow))
              (realUniformEmbeddingDecodeBHist (realUniformEmbeddingRawAt 1 flow))
              (realUniformEmbeddingDecodeBHist (realUniformEmbeddingRawAt 2 flow))
              (realUniformEmbeddingDecodeBHist (realUniformEmbeddingRawAt 3 flow))
              (realUniformEmbeddingDecodeBHist (realUniformEmbeddingRawAt 4 flow))
              (realUniformEmbeddingDecodeBHist (realUniformEmbeddingRawAt 5 flow))
              (realUniformEmbeddingDecodeBHist (realUniformEmbeddingRawAt 6 flow))
              (realUniformEmbeddingDecodeBHist (realUniformEmbeddingRawAt 7 flow))
              (realUniformEmbeddingDecodeBHist (realUniformEmbeddingRawAt 8 flow))
              (realUniformEmbeddingDecodeBHist (realUniformEmbeddingRawAt 9 flow)))
      | false => none

private theorem realUniformEmbedding_round_trip :
    ∀ x : RealUniformEmbeddingUp,
      realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W D Q E U H C P N =>
      change
        some
          (RealUniformEmbeddingUp.mk
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist S))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist W))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist D))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist Q))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist E))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist U))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist H))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist C))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist P))
            (realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist N))) =
          some (RealUniformEmbeddingUp.mk S W D Q E U H C P N)
      rw [realUniformEmbedding_decode_encode_bhist S,
        realUniformEmbedding_decode_encode_bhist W,
        realUniformEmbedding_decode_encode_bhist D,
        realUniformEmbedding_decode_encode_bhist Q,
        realUniformEmbedding_decode_encode_bhist E,
        realUniformEmbedding_decode_encode_bhist U,
        realUniformEmbedding_decode_encode_bhist H,
        realUniformEmbedding_decode_encode_bhist C,
        realUniformEmbedding_decode_encode_bhist P,
        realUniformEmbedding_decode_encode_bhist N]

private theorem realUniformEmbeddingToEventFlow_injective {x y : RealUniformEmbeddingUp} :
    realUniformEmbeddingToEventFlow x = realUniformEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow x) =
        realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow y) :=
    congrArg realUniformEmbeddingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realUniformEmbedding_round_trip x).symm
      (Eq.trans hread (realUniformEmbedding_round_trip y)))

private theorem realUniformEmbedding_field_faithful :
    ∀ x y : RealUniformEmbeddingUp,
      realUniformEmbeddingFields x = realUniformEmbeddingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 W1 D1 Q1 E1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 W2 D2 Q2 E2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realUniformEmbeddingBHistCarrier : BHistCarrier RealUniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realUniformEmbeddingToEventFlow
  fromEventFlow := realUniformEmbeddingFromEventFlow

instance realUniformEmbeddingChapterTasteGate : ChapterTasteGate RealUniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow x) = some x
    exact realUniformEmbedding_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realUniformEmbeddingToEventFlow_injective heq)

instance realUniformEmbeddingFieldFaithful : FieldFaithful RealUniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realUniformEmbeddingFields
  field_faithful := realUniformEmbedding_field_faithful

instance realUniformEmbeddingNontrivial : Nontrivial RealUniformEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealUniformEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealUniformEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealUniformEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realUniformEmbeddingChapterTasteGate

theorem RealUniformEmbeddingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealUniformEmbeddingUp) ∧
      Nonempty (FieldFaithful RealUniformEmbeddingUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RealUniformEmbeddingUp) ∧
      (∀ h : BHist,
        realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist h) = h) ∧
      (∀ x : RealUniformEmbeddingUp,
        realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow x) = some x) ∧
      (∀ x y : RealUniformEmbeddingUp,
        realUniformEmbeddingToEventFlow x = realUniformEmbeddingToEventFlow y → x = y) ∧
      realUniformEmbeddingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨Nonempty.intro realUniformEmbeddingChapterTasteGate,
      Nonempty.intro realUniformEmbeddingFieldFaithful,
      Nonempty.intro realUniformEmbeddingNontrivial,
      realUniformEmbedding_decode_encode_bhist,
      realUniformEmbedding_round_trip,
      (fun _ _ heq => realUniformEmbeddingToEventFlow_injective heq),
      rfl⟩

theorem RealUniformEmbeddingUp_single_carrier_alignment :
    (∀ h : BHist,
      realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist h) = h) ∧
      (∀ x : RealUniformEmbeddingUp,
        realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow x) = some x) ∧
      (∀ x y : RealUniformEmbeddingUp,
        realUniformEmbeddingToEventFlow x = realUniformEmbeddingToEventFlow y → x = y) ∧
      realUniformEmbeddingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨realUniformEmbedding_decode_encode_bhist,
      realUniformEmbedding_round_trip,
      (fun _ _ heq => realUniformEmbeddingToEventFlow_injective heq),
      rfl⟩

namespace TasteGate

theorem RealUniformEmbeddingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealUniformEmbeddingUp) ∧
      Nonempty (FieldFaithful RealUniformEmbeddingUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RealUniformEmbeddingUp) ∧
      (∀ h : BHist,
        realUniformEmbeddingDecodeBHist (realUniformEmbeddingEncodeBHist h) = h) ∧
      (∀ x : RealUniformEmbeddingUp,
        realUniformEmbeddingFromEventFlow (realUniformEmbeddingToEventFlow x) = some x) ∧
      (∀ x y : RealUniformEmbeddingUp,
        realUniformEmbeddingToEventFlow x = realUniformEmbeddingToEventFlow y → x = y) ∧
      realUniformEmbeddingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  exact
    BEDC.Derived.RealUniformEmbeddingUp.RealUniformEmbeddingTasteGate_single_carrier_alignment

end TasteGate

end BEDC.Derived.RealUniformEmbeddingUp
