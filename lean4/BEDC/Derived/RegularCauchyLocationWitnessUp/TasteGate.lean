import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocationWitnessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLocationWitnessUp : Type where
  | mk (R S D W E H C P N : BHist) : RegularCauchyLocationWitnessUp
  deriving DecidableEq

def regularCauchyLocationWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLocationWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLocationWitnessEncodeBHist h

def regularCauchyLocationWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLocationWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLocationWitnessDecodeBHist tail)

private theorem regularCauchyLocationWitness_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyLocationWitnessDecodeBHist
        (regularCauchyLocationWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLocationWitnessToEventFlow :
    RegularCauchyLocationWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLocationWitnessUp.mk R S D W E H C P N =>
      [[BMark.b0],
        regularCauchyLocationWitnessEncodeBHist R,
        [BMark.b1, BMark.b0],
        regularCauchyLocationWitnessEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocationWitnessEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocationWitnessEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocationWitnessEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocationWitnessEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyLocationWitnessEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyLocationWitnessEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyLocationWitnessEncodeBHist N]

private def regularCauchyLocationWitnessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyLocationWitnessEventAtDefault index rest

def regularCauchyLocationWitnessFromEventFlow
    (ef : EventFlow) : Option RegularCauchyLocationWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyLocationWitnessUp.mk
      (regularCauchyLocationWitnessDecodeBHist
        (regularCauchyLocationWitnessEventAtDefault 1 ef))
      (regularCauchyLocationWitnessDecodeBHist
        (regularCauchyLocationWitnessEventAtDefault 3 ef))
      (regularCauchyLocationWitnessDecodeBHist
        (regularCauchyLocationWitnessEventAtDefault 5 ef))
      (regularCauchyLocationWitnessDecodeBHist
        (regularCauchyLocationWitnessEventAtDefault 7 ef))
      (regularCauchyLocationWitnessDecodeBHist
        (regularCauchyLocationWitnessEventAtDefault 9 ef))
      (regularCauchyLocationWitnessDecodeBHist
        (regularCauchyLocationWitnessEventAtDefault 11 ef))
      (regularCauchyLocationWitnessDecodeBHist
        (regularCauchyLocationWitnessEventAtDefault 13 ef))
      (regularCauchyLocationWitnessDecodeBHist
        (regularCauchyLocationWitnessEventAtDefault 15 ef))
      (regularCauchyLocationWitnessDecodeBHist
        (regularCauchyLocationWitnessEventAtDefault 17 ef)))

private theorem regularCauchyLocationWitness_round_trip :
    ∀ x : RegularCauchyLocationWitnessUp,
      regularCauchyLocationWitnessFromEventFlow
        (regularCauchyLocationWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk R S D W E H C P N =>
      change
        some
          (RegularCauchyLocationWitnessUp.mk
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist R))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist S))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist D))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist W))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist E))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist H))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist C))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist P))
            (regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist N))) =
          some (RegularCauchyLocationWitnessUp.mk R S D W E H C P N)
      rw [regularCauchyLocationWitness_decode_encode_bhist R,
        regularCauchyLocationWitness_decode_encode_bhist S,
        regularCauchyLocationWitness_decode_encode_bhist D,
        regularCauchyLocationWitness_decode_encode_bhist W,
        regularCauchyLocationWitness_decode_encode_bhist E,
        regularCauchyLocationWitness_decode_encode_bhist H,
        regularCauchyLocationWitness_decode_encode_bhist C,
        regularCauchyLocationWitness_decode_encode_bhist P,
        regularCauchyLocationWitness_decode_encode_bhist N]

private theorem regularCauchyLocationWitnessToEventFlow_injective
    {x y : RegularCauchyLocationWitnessUp} :
    regularCauchyLocationWitnessToEventFlow x =
      regularCauchyLocationWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLocationWitnessFromEventFlow
          (regularCauchyLocationWitnessToEventFlow x) =
        regularCauchyLocationWitnessFromEventFlow
          (regularCauchyLocationWitnessToEventFlow y) :=
    congrArg regularCauchyLocationWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyLocationWitness_round_trip x).symm
      (Eq.trans hread (regularCauchyLocationWitness_round_trip y)))

private def regularCauchyLocationWitnessFields :
    RegularCauchyLocationWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLocationWitnessUp.mk R S D W E H C P N =>
      [R, S, D, W, E, H, C, P, N]

private theorem regularCauchyLocationWitness_field_faithful :
    ∀ x y : RegularCauchyLocationWitnessUp,
      regularCauchyLocationWitnessFields x =
        regularCauchyLocationWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token₁ token₂ hfields
  cases token₁ with
  | mk R₁ S₁ D₁ W₁ E₁ H₁ C₁ P₁ N₁ =>
      cases token₂ with
      | mk R₂ S₂ D₂ W₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyLocationWitnessBHistCarrier :
    BHistCarrier RegularCauchyLocationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLocationWitnessToEventFlow
  fromEventFlow := regularCauchyLocationWitnessFromEventFlow

instance regularCauchyLocationWitnessChapterTasteGate :
    ChapterTasteGate RegularCauchyLocationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyLocationWitnessFromEventFlow
      (regularCauchyLocationWitnessToEventFlow x) = some x
    exact regularCauchyLocationWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLocationWitnessToEventFlow_injective heq)

instance regularCauchyLocationWitnessFieldFaithful :
    FieldFaithful RegularCauchyLocationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyLocationWitnessFields
  field_faithful := regularCauchyLocationWitness_field_faithful

instance regularCauchyLocationWitnessNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyLocationWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyLocationWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyLocationWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyLocationWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLocationWitnessChapterTasteGate

private theorem RegularCauchyLocationWitnessTasteGate_single_carrier_alignment_instances :
    Nonempty (ChapterTasteGate RegularCauchyLocationWitnessUp) ∧
      Nonempty (FieldFaithful RegularCauchyLocationWitnessUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyLocationWitnessUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨regularCauchyLocationWitnessChapterTasteGate⟩,
      ⟨regularCauchyLocationWitnessFieldFaithful⟩,
      ⟨regularCauchyLocationWitnessNontrivial⟩⟩

theorem RegularCauchyLocationWitnessTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyLocationWitnessUp) ∧
      Nonempty (FieldFaithful RegularCauchyLocationWitnessUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyLocationWitnessUp) ∧
          (∀ h : BHist,
            regularCauchyLocationWitnessDecodeBHist
              (regularCauchyLocationWitnessEncodeBHist h) = h) ∧
            (∀ x : RegularCauchyLocationWitnessUp,
              regularCauchyLocationWitnessFromEventFlow
                (regularCauchyLocationWitnessToEventFlow x) = some x) ∧
              (∀ x y : RegularCauchyLocationWitnessUp,
                regularCauchyLocationWitnessToEventFlow x =
                  regularCauchyLocationWitnessToEventFlow y → x = y) ∧
                regularCauchyLocationWitnessEncodeBHist BHist.Empty =
                  ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  have hinstances :=
    RegularCauchyLocationWitnessTasteGate_single_carrier_alignment_instances
  exact
    ⟨hinstances.1,
      hinstances.2.1,
      hinstances.2.2,
      regularCauchyLocationWitness_decode_encode_bhist,
      regularCauchyLocationWitness_round_trip,
      (fun _ _ heq => regularCauchyLocationWitnessToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyLocationWitnessUp.TasteGate
