import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealRationalApproximationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealRationalApproximationUp : Type where
  | mk (R Q D S G A H C P N : BHist) : RealRationalApproximationUp
  deriving DecidableEq

def realRationalApproximationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realRationalApproximationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realRationalApproximationEncodeBHist h

def realRationalApproximationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realRationalApproximationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realRationalApproximationDecodeBHist tail)

private theorem realRationalApproximation_decode_encode_bhist :
    ∀ h : BHist,
      realRationalApproximationDecodeBHist (realRationalApproximationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def realRationalApproximationFields :
    RealRationalApproximationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealRationalApproximationUp.mk R Q D S G A H C P N => [R, Q, D, S, G, A, H, C, P, N]

def realRationalApproximationToEventFlow :
    RealRationalApproximationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realRationalApproximationFields x).map realRationalApproximationEncodeBHist

private def realRationalApproximationRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => realRationalApproximationRawAt n rest

private def realRationalApproximationLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => realRationalApproximationLengthEq n rest

def realRationalApproximationFromEventFlow :
    EventFlow → Option RealRationalApproximationUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match realRationalApproximationLengthEq 10 flow with
      | true =>
          some
            (RealRationalApproximationUp.mk
              (realRationalApproximationDecodeBHist (realRationalApproximationRawAt 0 flow))
              (realRationalApproximationDecodeBHist (realRationalApproximationRawAt 1 flow))
              (realRationalApproximationDecodeBHist (realRationalApproximationRawAt 2 flow))
              (realRationalApproximationDecodeBHist (realRationalApproximationRawAt 3 flow))
              (realRationalApproximationDecodeBHist (realRationalApproximationRawAt 4 flow))
              (realRationalApproximationDecodeBHist (realRationalApproximationRawAt 5 flow))
              (realRationalApproximationDecodeBHist (realRationalApproximationRawAt 6 flow))
              (realRationalApproximationDecodeBHist (realRationalApproximationRawAt 7 flow))
              (realRationalApproximationDecodeBHist (realRationalApproximationRawAt 8 flow))
              (realRationalApproximationDecodeBHist (realRationalApproximationRawAt 9 flow)))
      | false => none

private theorem realRationalApproximation_round_trip :
    ∀ x : RealRationalApproximationUp,
      realRationalApproximationFromEventFlow
          (realRationalApproximationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R Q D S G A H C P N =>
      change
        some
          (RealRationalApproximationUp.mk
            (realRationalApproximationDecodeBHist (realRationalApproximationEncodeBHist R))
            (realRationalApproximationDecodeBHist (realRationalApproximationEncodeBHist Q))
            (realRationalApproximationDecodeBHist (realRationalApproximationEncodeBHist D))
            (realRationalApproximationDecodeBHist (realRationalApproximationEncodeBHist S))
            (realRationalApproximationDecodeBHist (realRationalApproximationEncodeBHist G))
            (realRationalApproximationDecodeBHist (realRationalApproximationEncodeBHist A))
            (realRationalApproximationDecodeBHist (realRationalApproximationEncodeBHist H))
            (realRationalApproximationDecodeBHist (realRationalApproximationEncodeBHist C))
            (realRationalApproximationDecodeBHist (realRationalApproximationEncodeBHist P))
            (realRationalApproximationDecodeBHist (realRationalApproximationEncodeBHist N))) =
          some (RealRationalApproximationUp.mk R Q D S G A H C P N)
      rw [realRationalApproximation_decode_encode_bhist R,
        realRationalApproximation_decode_encode_bhist Q,
        realRationalApproximation_decode_encode_bhist D,
        realRationalApproximation_decode_encode_bhist S,
        realRationalApproximation_decode_encode_bhist G,
        realRationalApproximation_decode_encode_bhist A,
        realRationalApproximation_decode_encode_bhist H,
        realRationalApproximation_decode_encode_bhist C,
        realRationalApproximation_decode_encode_bhist P,
        realRationalApproximation_decode_encode_bhist N]

private theorem realRationalApproximationToEventFlow_injective
    {x y : RealRationalApproximationUp} :
    realRationalApproximationToEventFlow x =
        realRationalApproximationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realRationalApproximationFromEventFlow
          (realRationalApproximationToEventFlow x) =
        realRationalApproximationFromEventFlow
          (realRationalApproximationToEventFlow y) :=
    congrArg realRationalApproximationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realRationalApproximation_round_trip x).symm
      (Eq.trans hread (realRationalApproximation_round_trip y)))

private theorem realRationalApproximation_field_faithful :
    ∀ x y : RealRationalApproximationUp,
      realRationalApproximationFields x = realRationalApproximationFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 Q1 D1 S1 G1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 Q2 D2 S2 G2 A2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance realRationalApproximationBHistCarrier :
    BHistCarrier RealRationalApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realRationalApproximationToEventFlow
  fromEventFlow := realRationalApproximationFromEventFlow

instance realRationalApproximationChapterTasteGate :
    ChapterTasteGate RealRationalApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realRationalApproximationFromEventFlow
          (realRationalApproximationToEventFlow x) =
        some x
    exact realRationalApproximation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realRationalApproximationToEventFlow_injective heq)

instance realRationalApproximationFieldFaithful :
    FieldFaithful RealRationalApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realRationalApproximationFields
  field_faithful := realRationalApproximation_field_faithful

instance realRationalApproximationNontrivial :
    Nontrivial RealRationalApproximationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealRationalApproximationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealRationalApproximationUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealRationalApproximationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realRationalApproximationChapterTasteGate

theorem RealRationalApproximationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealRationalApproximationUp) ∧
      Nonempty (FieldFaithful RealRationalApproximationUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RealRationalApproximationUp) ∧
      (∀ h : BHist,
        realRationalApproximationDecodeBHist (realRationalApproximationEncodeBHist h) = h) ∧
      (∀ x : RealRationalApproximationUp,
        realRationalApproximationFromEventFlow (realRationalApproximationToEventFlow x) =
          some x) ∧
      (∀ x y : RealRationalApproximationUp,
        realRationalApproximationToEventFlow x = realRationalApproximationToEventFlow y →
          x = y) ∧
      realRationalApproximationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨Nonempty.intro realRationalApproximationChapterTasteGate,
      Nonempty.intro realRationalApproximationFieldFaithful,
      Nonempty.intro realRationalApproximationNontrivial,
      realRationalApproximation_decode_encode_bhist,
      realRationalApproximation_round_trip,
      (fun _ _ heq => realRationalApproximationToEventFlow_injective heq),
      rfl⟩

namespace TasteGate

theorem RealRationalApproximationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealRationalApproximationUp) ∧
      Nonempty (FieldFaithful RealRationalApproximationUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial RealRationalApproximationUp) ∧
      (∀ h : BHist,
        realRationalApproximationDecodeBHist (realRationalApproximationEncodeBHist h) = h) ∧
      (∀ x : RealRationalApproximationUp,
        realRationalApproximationFromEventFlow (realRationalApproximationToEventFlow x) =
          some x) ∧
      (∀ x y : RealRationalApproximationUp,
        realRationalApproximationToEventFlow x = realRationalApproximationToEventFlow y →
          x = y) ∧
      realRationalApproximationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  exact BEDC.Derived.RealRationalApproximationUp.RealRationalApproximationTasteGate_single_carrier_alignment

end TasteGate

end BEDC.Derived.RealRationalApproximationUp
