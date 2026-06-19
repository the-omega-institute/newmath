import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannRefinementCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannRefinementCriterionUp : Type where
  | mk (I T U G C M D W E H K P N : BHist) : RiemannRefinementCriterionUp
  deriving DecidableEq

def RiemannRefinementCriterion_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: RiemannRefinementCriterion_encodeBHist h
  | BHist.e1 h => BMark.b1 :: RiemannRefinementCriterion_encodeBHist h

def RiemannRefinementCriterion_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (RiemannRefinementCriterion_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (RiemannRefinementCriterion_decodeBHist tail)

private theorem RiemannRefinementCriterion_decode_encode :
    ∀ h : BHist,
      RiemannRefinementCriterion_decodeBHist
          (RiemannRefinementCriterion_encodeBHist h) =
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

def RiemannRefinementCriterion_fields : RiemannRefinementCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannRefinementCriterionUp.mk I T U G C M D W E H K P N =>
      [I, T, U, G, C, M, D, W, E, H, K, P, N]

def RiemannRefinementCriterion_toEventFlow : RiemannRefinementCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannRefinementCriterionUp.mk I T U G C M D W E H K P N =>
      [RiemannRefinementCriterion_encodeBHist I,
        RiemannRefinementCriterion_encodeBHist T,
        RiemannRefinementCriterion_encodeBHist U,
        RiemannRefinementCriterion_encodeBHist G,
        RiemannRefinementCriterion_encodeBHist C,
        RiemannRefinementCriterion_encodeBHist M,
        RiemannRefinementCriterion_encodeBHist D,
        RiemannRefinementCriterion_encodeBHist W,
        RiemannRefinementCriterion_encodeBHist E,
        RiemannRefinementCriterion_encodeBHist H,
        RiemannRefinementCriterion_encodeBHist K,
        RiemannRefinementCriterion_encodeBHist P,
        RiemannRefinementCriterion_encodeBHist N]

private def RiemannRefinementCriterion_rawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => RiemannRefinementCriterion_rawAt n rest

private def RiemannRefinementCriterion_lengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => RiemannRefinementCriterion_lengthEq n rest

def RiemannRefinementCriterion_fromEventFlow :
    EventFlow → Option RiemannRefinementCriterionUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match RiemannRefinementCriterion_lengthEq 13 flow with
      | true =>
          some
            (RiemannRefinementCriterionUp.mk
              (RiemannRefinementCriterion_decodeBHist
                (RiemannRefinementCriterion_rawAt 0 flow))
              (RiemannRefinementCriterion_decodeBHist
                (RiemannRefinementCriterion_rawAt 1 flow))
              (RiemannRefinementCriterion_decodeBHist
                (RiemannRefinementCriterion_rawAt 2 flow))
              (RiemannRefinementCriterion_decodeBHist
                (RiemannRefinementCriterion_rawAt 3 flow))
              (RiemannRefinementCriterion_decodeBHist
                (RiemannRefinementCriterion_rawAt 4 flow))
              (RiemannRefinementCriterion_decodeBHist
                (RiemannRefinementCriterion_rawAt 5 flow))
              (RiemannRefinementCriterion_decodeBHist
                (RiemannRefinementCriterion_rawAt 6 flow))
              (RiemannRefinementCriterion_decodeBHist
                (RiemannRefinementCriterion_rawAt 7 flow))
              (RiemannRefinementCriterion_decodeBHist
                (RiemannRefinementCriterion_rawAt 8 flow))
              (RiemannRefinementCriterion_decodeBHist
                (RiemannRefinementCriterion_rawAt 9 flow))
              (RiemannRefinementCriterion_decodeBHist
                (RiemannRefinementCriterion_rawAt 10 flow))
              (RiemannRefinementCriterion_decodeBHist
                (RiemannRefinementCriterion_rawAt 11 flow))
              (RiemannRefinementCriterion_decodeBHist
                (RiemannRefinementCriterion_rawAt 12 flow)))
      | false => none

private theorem RiemannRefinementCriterion_round_trip :
    ∀ x : RiemannRefinementCriterionUp,
      RiemannRefinementCriterion_fromEventFlow
          (RiemannRefinementCriterion_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I T U G C M D W E H K P N =>
      change
        some
          (RiemannRefinementCriterionUp.mk
            (RiemannRefinementCriterion_decodeBHist
              (RiemannRefinementCriterion_encodeBHist I))
            (RiemannRefinementCriterion_decodeBHist
              (RiemannRefinementCriterion_encodeBHist T))
            (RiemannRefinementCriterion_decodeBHist
              (RiemannRefinementCriterion_encodeBHist U))
            (RiemannRefinementCriterion_decodeBHist
              (RiemannRefinementCriterion_encodeBHist G))
            (RiemannRefinementCriterion_decodeBHist
              (RiemannRefinementCriterion_encodeBHist C))
            (RiemannRefinementCriterion_decodeBHist
              (RiemannRefinementCriterion_encodeBHist M))
            (RiemannRefinementCriterion_decodeBHist
              (RiemannRefinementCriterion_encodeBHist D))
            (RiemannRefinementCriterion_decodeBHist
              (RiemannRefinementCriterion_encodeBHist W))
            (RiemannRefinementCriterion_decodeBHist
              (RiemannRefinementCriterion_encodeBHist E))
            (RiemannRefinementCriterion_decodeBHist
              (RiemannRefinementCriterion_encodeBHist H))
            (RiemannRefinementCriterion_decodeBHist
              (RiemannRefinementCriterion_encodeBHist K))
            (RiemannRefinementCriterion_decodeBHist
              (RiemannRefinementCriterion_encodeBHist P))
            (RiemannRefinementCriterion_decodeBHist
              (RiemannRefinementCriterion_encodeBHist N))) =
          some (RiemannRefinementCriterionUp.mk I T U G C M D W E H K P N)
      rw [RiemannRefinementCriterion_decode_encode I,
        RiemannRefinementCriterion_decode_encode T,
        RiemannRefinementCriterion_decode_encode U,
        RiemannRefinementCriterion_decode_encode G,
        RiemannRefinementCriterion_decode_encode C,
        RiemannRefinementCriterion_decode_encode M,
        RiemannRefinementCriterion_decode_encode D,
        RiemannRefinementCriterion_decode_encode W,
        RiemannRefinementCriterion_decode_encode E,
        RiemannRefinementCriterion_decode_encode H,
        RiemannRefinementCriterion_decode_encode K,
        RiemannRefinementCriterion_decode_encode P,
        RiemannRefinementCriterion_decode_encode N]

private theorem RiemannRefinementCriterion_toEventFlow_injective
    {x y : RiemannRefinementCriterionUp} :
    RiemannRefinementCriterion_toEventFlow x =
        RiemannRefinementCriterion_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      RiemannRefinementCriterion_fromEventFlow
          (RiemannRefinementCriterion_toEventFlow x) =
        RiemannRefinementCriterion_fromEventFlow
          (RiemannRefinementCriterion_toEventFlow y) :=
    congrArg RiemannRefinementCriterion_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RiemannRefinementCriterion_round_trip x).symm
      (Eq.trans hread (RiemannRefinementCriterion_round_trip y)))

private theorem RiemannRefinementCriterion_field_faithful :
    ∀ x y : RiemannRefinementCriterionUp,
      RiemannRefinementCriterion_fields x = RiemannRefinementCriterion_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk I1 T1 U1 G1 C1 M1 D1 W1 E1 H1 K1 P1 N1 =>
      cases y with
      | mk I2 T2 U2 G2 C2 M2 D2 W2 E2 H2 K2 P2 N2 =>
          cases h
          rfl

instance RiemannRefinementCriterionBHistCarrier :
    BHistCarrier RiemannRefinementCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := RiemannRefinementCriterion_toEventFlow
  fromEventFlow := RiemannRefinementCriterion_fromEventFlow

instance RiemannRefinementCriterionChapterTasteGate :
    ChapterTasteGate RiemannRefinementCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      RiemannRefinementCriterion_fromEventFlow
          (RiemannRefinementCriterion_toEventFlow x) =
        some x
    exact RiemannRefinementCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RiemannRefinementCriterion_toEventFlow_injective heq)

instance RiemannRefinementCriterionFieldFaithful :
    FieldFaithful RiemannRefinementCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := RiemannRefinementCriterion_fields
  field_faithful := RiemannRefinementCriterion_field_faithful

instance RiemannRefinementCriterionNontrivial :
    Nontrivial RiemannRefinementCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RiemannRefinementCriterionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RiemannRefinementCriterionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RiemannRefinementCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RiemannRefinementCriterionChapterTasteGate

theorem RiemannRefinementCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      RiemannRefinementCriterion_decodeBHist
          (RiemannRefinementCriterion_encodeBHist h) =
        h) ∧
      RiemannRefinementCriterion_encodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        Nonempty (BHistCarrier RiemannRefinementCriterionUp) ∧
          Nonempty (ChapterTasteGate RiemannRefinementCriterionUp) ∧
            Nonempty (FieldFaithful RiemannRefinementCriterionUp) ∧
              Nonempty (Nontrivial RiemannRefinementCriterionUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RiemannRefinementCriterion_decode_encode,
      rfl,
      ⟨RiemannRefinementCriterionBHistCarrier⟩,
      ⟨RiemannRefinementCriterionChapterTasteGate⟩,
      ⟨RiemannRefinementCriterionFieldFaithful⟩,
      ⟨RiemannRefinementCriterionNontrivial⟩⟩

end BEDC.Derived.RiemannRefinementCriterionUp
