import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannIntegrabilityCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannIntegrabilityCriterionUp : Type where
  | mk (P S G R B Q E H C V N : BHist) : RiemannIntegrabilityCriterionUp
  deriving DecidableEq

def riemannIntegrabilityCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannIntegrabilityCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannIntegrabilityCriterionEncodeBHist h

def riemannIntegrabilityCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannIntegrabilityCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannIntegrabilityCriterionDecodeBHist tail)

private theorem riemannIntegrabilityCriterion_decode_encode_bhist :
    ∀ h : BHist,
      riemannIntegrabilityCriterionDecodeBHist
          (riemannIntegrabilityCriterionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def riemannIntegrabilityCriterionFields :
    RiemannIntegrabilityCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannIntegrabilityCriterionUp.mk P S G R B Q E H C V N =>
      [P, S, G, R, B, Q, E, H, C, V, N]

def riemannIntegrabilityCriterionToEventFlow :
    RiemannIntegrabilityCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (riemannIntegrabilityCriterionFields x).map
      riemannIntegrabilityCriterionEncodeBHist

private def riemannIntegrabilityCriterionRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => riemannIntegrabilityCriterionRawAt n rest

private def riemannIntegrabilityCriterionLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => riemannIntegrabilityCriterionLengthEq n rest

def riemannIntegrabilityCriterionFromEventFlow :
    EventFlow → Option RiemannIntegrabilityCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match riemannIntegrabilityCriterionLengthEq 11 flow with
      | true =>
          some
            (RiemannIntegrabilityCriterionUp.mk
              (riemannIntegrabilityCriterionDecodeBHist
                (riemannIntegrabilityCriterionRawAt 0 flow))
              (riemannIntegrabilityCriterionDecodeBHist
                (riemannIntegrabilityCriterionRawAt 1 flow))
              (riemannIntegrabilityCriterionDecodeBHist
                (riemannIntegrabilityCriterionRawAt 2 flow))
              (riemannIntegrabilityCriterionDecodeBHist
                (riemannIntegrabilityCriterionRawAt 3 flow))
              (riemannIntegrabilityCriterionDecodeBHist
                (riemannIntegrabilityCriterionRawAt 4 flow))
              (riemannIntegrabilityCriterionDecodeBHist
                (riemannIntegrabilityCriterionRawAt 5 flow))
              (riemannIntegrabilityCriterionDecodeBHist
                (riemannIntegrabilityCriterionRawAt 6 flow))
              (riemannIntegrabilityCriterionDecodeBHist
                (riemannIntegrabilityCriterionRawAt 7 flow))
              (riemannIntegrabilityCriterionDecodeBHist
                (riemannIntegrabilityCriterionRawAt 8 flow))
              (riemannIntegrabilityCriterionDecodeBHist
                (riemannIntegrabilityCriterionRawAt 9 flow))
              (riemannIntegrabilityCriterionDecodeBHist
                (riemannIntegrabilityCriterionRawAt 10 flow)))
      | false => none

private theorem riemannIntegrabilityCriterion_round_trip :
    ∀ x : RiemannIntegrabilityCriterionUp,
      riemannIntegrabilityCriterionFromEventFlow
          (riemannIntegrabilityCriterionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P S G R B Q E H C V N =>
      change
        some
          (RiemannIntegrabilityCriterionUp.mk
            (riemannIntegrabilityCriterionDecodeBHist
              (riemannIntegrabilityCriterionEncodeBHist P))
            (riemannIntegrabilityCriterionDecodeBHist
              (riemannIntegrabilityCriterionEncodeBHist S))
            (riemannIntegrabilityCriterionDecodeBHist
              (riemannIntegrabilityCriterionEncodeBHist G))
            (riemannIntegrabilityCriterionDecodeBHist
              (riemannIntegrabilityCriterionEncodeBHist R))
            (riemannIntegrabilityCriterionDecodeBHist
              (riemannIntegrabilityCriterionEncodeBHist B))
            (riemannIntegrabilityCriterionDecodeBHist
              (riemannIntegrabilityCriterionEncodeBHist Q))
            (riemannIntegrabilityCriterionDecodeBHist
              (riemannIntegrabilityCriterionEncodeBHist E))
            (riemannIntegrabilityCriterionDecodeBHist
              (riemannIntegrabilityCriterionEncodeBHist H))
            (riemannIntegrabilityCriterionDecodeBHist
              (riemannIntegrabilityCriterionEncodeBHist C))
            (riemannIntegrabilityCriterionDecodeBHist
              (riemannIntegrabilityCriterionEncodeBHist V))
            (riemannIntegrabilityCriterionDecodeBHist
              (riemannIntegrabilityCriterionEncodeBHist N))) =
          some (RiemannIntegrabilityCriterionUp.mk P S G R B Q E H C V N)
      rw [riemannIntegrabilityCriterion_decode_encode_bhist P,
        riemannIntegrabilityCriterion_decode_encode_bhist S,
        riemannIntegrabilityCriterion_decode_encode_bhist G,
        riemannIntegrabilityCriterion_decode_encode_bhist R,
        riemannIntegrabilityCriterion_decode_encode_bhist B,
        riemannIntegrabilityCriterion_decode_encode_bhist Q,
        riemannIntegrabilityCriterion_decode_encode_bhist E,
        riemannIntegrabilityCriterion_decode_encode_bhist H,
        riemannIntegrabilityCriterion_decode_encode_bhist C,
        riemannIntegrabilityCriterion_decode_encode_bhist V,
        riemannIntegrabilityCriterion_decode_encode_bhist N]

private theorem riemannIntegrabilityCriterionToEventFlow_injective
    {x y : RiemannIntegrabilityCriterionUp} :
    riemannIntegrabilityCriterionToEventFlow x =
        riemannIntegrabilityCriterionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      riemannIntegrabilityCriterionFromEventFlow
          (riemannIntegrabilityCriterionToEventFlow x) =
        riemannIntegrabilityCriterionFromEventFlow
          (riemannIntegrabilityCriterionToEventFlow y) :=
    congrArg riemannIntegrabilityCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (riemannIntegrabilityCriterion_round_trip x).symm
      (Eq.trans hread (riemannIntegrabilityCriterion_round_trip y)))

private theorem riemannIntegrabilityCriterion_field_faithful :
    ∀ x y : RiemannIntegrabilityCriterionUp,
      riemannIntegrabilityCriterionFields x =
          riemannIntegrabilityCriterionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P1 S1 G1 R1 B1 Q1 E1 H1 C1 V1 N1 =>
      cases y with
      | mk P2 S2 G2 R2 B2 Q2 E2 H2 C2 V2 N2 =>
          cases hfields
          rfl

instance riemannIntegrabilityCriterionBHistCarrier :
    BHistCarrier RiemannIntegrabilityCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannIntegrabilityCriterionToEventFlow
  fromEventFlow := riemannIntegrabilityCriterionFromEventFlow

instance riemannIntegrabilityCriterionChapterTasteGate :
    ChapterTasteGate RiemannIntegrabilityCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      riemannIntegrabilityCriterionFromEventFlow
          (riemannIntegrabilityCriterionToEventFlow x) =
        some x
    exact riemannIntegrabilityCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (riemannIntegrabilityCriterionToEventFlow_injective heq)

instance riemannIntegrabilityCriterionFieldFaithful :
    FieldFaithful RiemannIntegrabilityCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := riemannIntegrabilityCriterionFields
  field_faithful := riemannIntegrabilityCriterion_field_faithful

instance riemannIntegrabilityCriterionNontrivial :
    Nontrivial RiemannIntegrabilityCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RiemannIntegrabilityCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RiemannIntegrabilityCriterionUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RiemannIntegrabilityCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  riemannIntegrabilityCriterionChapterTasteGate

theorem RiemannIntegrabilityCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      riemannIntegrabilityCriterionDecodeBHist
          (riemannIntegrabilityCriterionEncodeBHist h) =
        h) ∧
      (∀ x : RiemannIntegrabilityCriterionUp,
        riemannIntegrabilityCriterionFromEventFlow
            (riemannIntegrabilityCriterionToEventFlow x) =
          some x) ∧
      (∀ x y : RiemannIntegrabilityCriterionUp,
        riemannIntegrabilityCriterionToEventFlow x =
            riemannIntegrabilityCriterionToEventFlow y →
          x = y) ∧
      riemannIntegrabilityCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨riemannIntegrabilityCriterion_decode_encode_bhist,
      riemannIntegrabilityCriterion_round_trip,
      (fun _ _ heq => riemannIntegrabilityCriterionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RiemannIntegrabilityCriterionUp
