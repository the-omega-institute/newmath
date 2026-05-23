import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyBallUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyBallUp : Type where
  | mk (X C R W D Q S H T P N : BHist) : RegularCauchyBallUp
  deriving DecidableEq

def regularCauchyBallEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyBallEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyBallEncodeBHist h

def regularCauchyBallDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyBallDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyBallDecodeBHist tail)

private theorem regularCauchyBall_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyBallToEventFlow : RegularCauchyBallUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyBallUp.mk X C R W D Q S H T P N =>
      [[BMark.b0],
        regularCauchyBallEncodeBHist X,
        [BMark.b1, BMark.b0],
        regularCauchyBallEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyBallEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyBallEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyBallEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyBallEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyBallEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyBallEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyBallEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyBallEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyBallEncodeBHist N]

private def regularCauchyBallEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyBallEventAtDefault index rest

def regularCauchyBallFromEventFlow
    (ef : EventFlow) : Option RegularCauchyBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyBallUp.mk
      (regularCauchyBallDecodeBHist (regularCauchyBallEventAtDefault 1 ef))
      (regularCauchyBallDecodeBHist (regularCauchyBallEventAtDefault 3 ef))
      (regularCauchyBallDecodeBHist (regularCauchyBallEventAtDefault 5 ef))
      (regularCauchyBallDecodeBHist (regularCauchyBallEventAtDefault 7 ef))
      (regularCauchyBallDecodeBHist (regularCauchyBallEventAtDefault 9 ef))
      (regularCauchyBallDecodeBHist (regularCauchyBallEventAtDefault 11 ef))
      (regularCauchyBallDecodeBHist (regularCauchyBallEventAtDefault 13 ef))
      (regularCauchyBallDecodeBHist (regularCauchyBallEventAtDefault 15 ef))
      (regularCauchyBallDecodeBHist (regularCauchyBallEventAtDefault 17 ef))
      (regularCauchyBallDecodeBHist (regularCauchyBallEventAtDefault 19 ef))
      (regularCauchyBallDecodeBHist (regularCauchyBallEventAtDefault 21 ef)))

private theorem regularCauchyBall_round_trip :
    ∀ x : RegularCauchyBallUp,
      regularCauchyBallFromEventFlow (regularCauchyBallToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X C R W D Q S H T P N =>
      change
        some
          (RegularCauchyBallUp.mk
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist X))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist C))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist R))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist W))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist D))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist Q))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist S))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist H))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist T))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist P))
            (regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist N))) =
          some (RegularCauchyBallUp.mk X C R W D Q S H T P N)
      rw [regularCauchyBall_decode_encode_bhist X,
        regularCauchyBall_decode_encode_bhist C,
        regularCauchyBall_decode_encode_bhist R,
        regularCauchyBall_decode_encode_bhist W,
        regularCauchyBall_decode_encode_bhist D,
        regularCauchyBall_decode_encode_bhist Q,
        regularCauchyBall_decode_encode_bhist S,
        regularCauchyBall_decode_encode_bhist H,
        regularCauchyBall_decode_encode_bhist T,
        regularCauchyBall_decode_encode_bhist P,
        regularCauchyBall_decode_encode_bhist N]

private theorem regularCauchyBallToEventFlow_injective {x y : RegularCauchyBallUp} :
    regularCauchyBallToEventFlow x = regularCauchyBallToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyBallFromEventFlow (regularCauchyBallToEventFlow x) =
        regularCauchyBallFromEventFlow (regularCauchyBallToEventFlow y) :=
    congrArg regularCauchyBallFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyBall_round_trip x).symm
      (Eq.trans hread (regularCauchyBall_round_trip y)))

private def regularCauchyBallFields : RegularCauchyBallUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyBallUp.mk X C R W D Q S H T P N => [X, C, R, W, D, Q, S, H, T, P, N]

private theorem regularCauchyBall_field_faithful :
    ∀ x y : RegularCauchyBallUp,
      regularCauchyBallFields x = regularCauchyBallFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token₁ token₂ hfields
  cases token₁ with
  | mk X₁ C₁ R₁ W₁ D₁ Q₁ S₁ H₁ T₁ P₁ N₁ =>
      cases token₂ with
      | mk X₂ C₂ R₂ W₂ D₂ Q₂ S₂ H₂ T₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyBallBHistCarrier : BHistCarrier RegularCauchyBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyBallToEventFlow
  fromEventFlow := regularCauchyBallFromEventFlow

instance regularCauchyBallChapterTasteGate :
    ChapterTasteGate RegularCauchyBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyBallFromEventFlow (regularCauchyBallToEventFlow x) = some x
    exact regularCauchyBall_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyBallToEventFlow_injective heq)

instance regularCauchyBallFieldFaithful : FieldFaithful RegularCauchyBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyBallFields
  field_faithful := regularCauchyBall_field_faithful

instance regularCauchyBallNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyBallUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyBallUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RegularCauchyBallUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyBallUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyBallChapterTasteGate

private theorem RegularCauchyBallTasteGate_single_carrier_alignment_instances :
    Nonempty (ChapterTasteGate RegularCauchyBallUp) ∧
      Nonempty (FieldFaithful RegularCauchyBallUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyBallUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨regularCauchyBallChapterTasteGate⟩,
      ⟨regularCauchyBallFieldFaithful⟩,
      ⟨regularCauchyBallNontrivial⟩⟩

theorem RegularCauchyBallTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyBallUp) ∧
      Nonempty (FieldFaithful RegularCauchyBallUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyBallUp) ∧
          (∀ h : BHist,
            regularCauchyBallDecodeBHist (regularCauchyBallEncodeBHist h) = h) ∧
            (∀ x : RegularCauchyBallUp,
              regularCauchyBallFromEventFlow (regularCauchyBallToEventFlow x) =
                some x) ∧
              (∀ x y : RegularCauchyBallUp,
                regularCauchyBallToEventFlow x =
                  regularCauchyBallToEventFlow y → x = y) ∧
                regularCauchyBallEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  have hinstances :=
    RegularCauchyBallTasteGate_single_carrier_alignment_instances
  exact
    ⟨hinstances.1,
      hinstances.2.1,
      hinstances.2.2,
      regularCauchyBall_decode_encode_bhist,
      regularCauchyBall_round_trip,
      (fun _ _ heq => regularCauchyBallToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyBallUp.TasteGate
