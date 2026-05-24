import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyExtensionalityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyExtensionalityUp : Type where
  | mk (R0 R1 S0 S1 D T A0 A1 H C P N : BHist) : RegularCauchyExtensionalityUp
  deriving DecidableEq

def regularCauchyExtensionalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyExtensionalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyExtensionalityEncodeBHist h

def regularCauchyExtensionalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyExtensionalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyExtensionalityDecodeBHist tail)

private theorem regularCauchyExtensionality_decode_encode :
    ∀ h : BHist,
      regularCauchyExtensionalityDecodeBHist
          (regularCauchyExtensionalityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyExtensionalityFields :
    RegularCauchyExtensionalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyExtensionalityUp.mk R0 R1 S0 S1 D T A0 A1 H C P N =>
      [R0, R1, S0, S1, D, T, A0, A1, H, C, P, N]

def regularCauchyExtensionalityToEventFlow :
    RegularCauchyExtensionalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map regularCauchyExtensionalityEncodeBHist
        (regularCauchyExtensionalityFields x)

private def regularCauchyExtensionalityRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyExtensionalityRawAt index rest

def regularCauchyExtensionalityFromEventFlow
    (flow : EventFlow) : Option RegularCauchyExtensionalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyExtensionalityUp.mk
      (regularCauchyExtensionalityDecodeBHist (regularCauchyExtensionalityRawAt 0 flow))
      (regularCauchyExtensionalityDecodeBHist (regularCauchyExtensionalityRawAt 1 flow))
      (regularCauchyExtensionalityDecodeBHist (regularCauchyExtensionalityRawAt 2 flow))
      (regularCauchyExtensionalityDecodeBHist (regularCauchyExtensionalityRawAt 3 flow))
      (regularCauchyExtensionalityDecodeBHist (regularCauchyExtensionalityRawAt 4 flow))
      (regularCauchyExtensionalityDecodeBHist (regularCauchyExtensionalityRawAt 5 flow))
      (regularCauchyExtensionalityDecodeBHist (regularCauchyExtensionalityRawAt 6 flow))
      (regularCauchyExtensionalityDecodeBHist (regularCauchyExtensionalityRawAt 7 flow))
      (regularCauchyExtensionalityDecodeBHist (regularCauchyExtensionalityRawAt 8 flow))
      (regularCauchyExtensionalityDecodeBHist (regularCauchyExtensionalityRawAt 9 flow))
      (regularCauchyExtensionalityDecodeBHist (regularCauchyExtensionalityRawAt 10 flow))
      (regularCauchyExtensionalityDecodeBHist (regularCauchyExtensionalityRawAt 11 flow)))

private theorem regularCauchyExtensionality_round_trip :
    ∀ x : RegularCauchyExtensionalityUp,
      regularCauchyExtensionalityFromEventFlow
          (regularCauchyExtensionalityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 S0 S1 D T A0 A1 H C P N =>
      change
        some
          (RegularCauchyExtensionalityUp.mk
            (regularCauchyExtensionalityDecodeBHist
              (regularCauchyExtensionalityEncodeBHist R0))
            (regularCauchyExtensionalityDecodeBHist
              (regularCauchyExtensionalityEncodeBHist R1))
            (regularCauchyExtensionalityDecodeBHist
              (regularCauchyExtensionalityEncodeBHist S0))
            (regularCauchyExtensionalityDecodeBHist
              (regularCauchyExtensionalityEncodeBHist S1))
            (regularCauchyExtensionalityDecodeBHist
              (regularCauchyExtensionalityEncodeBHist D))
            (regularCauchyExtensionalityDecodeBHist
              (regularCauchyExtensionalityEncodeBHist T))
            (regularCauchyExtensionalityDecodeBHist
              (regularCauchyExtensionalityEncodeBHist A0))
            (regularCauchyExtensionalityDecodeBHist
              (regularCauchyExtensionalityEncodeBHist A1))
            (regularCauchyExtensionalityDecodeBHist
              (regularCauchyExtensionalityEncodeBHist H))
            (regularCauchyExtensionalityDecodeBHist
              (regularCauchyExtensionalityEncodeBHist C))
            (regularCauchyExtensionalityDecodeBHist
              (regularCauchyExtensionalityEncodeBHist P))
            (regularCauchyExtensionalityDecodeBHist
              (regularCauchyExtensionalityEncodeBHist N))) =
          some (RegularCauchyExtensionalityUp.mk R0 R1 S0 S1 D T A0 A1 H C P N)
      rw [regularCauchyExtensionality_decode_encode R0,
        regularCauchyExtensionality_decode_encode R1,
        regularCauchyExtensionality_decode_encode S0,
        regularCauchyExtensionality_decode_encode S1,
        regularCauchyExtensionality_decode_encode D,
        regularCauchyExtensionality_decode_encode T,
        regularCauchyExtensionality_decode_encode A0,
        regularCauchyExtensionality_decode_encode A1,
        regularCauchyExtensionality_decode_encode H,
        regularCauchyExtensionality_decode_encode C,
        regularCauchyExtensionality_decode_encode P,
        regularCauchyExtensionality_decode_encode N]

private theorem regularCauchyExtensionalityToEventFlow_injective
    {x y : RegularCauchyExtensionalityUp} :
    regularCauchyExtensionalityToEventFlow x =
        regularCauchyExtensionalityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyExtensionalityFromEventFlow
          (regularCauchyExtensionalityToEventFlow x) =
        regularCauchyExtensionalityFromEventFlow
          (regularCauchyExtensionalityToEventFlow y) :=
    congrArg regularCauchyExtensionalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyExtensionality_round_trip x).symm
      (Eq.trans hread (regularCauchyExtensionality_round_trip y)))

private theorem regularCauchyExtensionality_fields_faithful :
    ∀ x y : RegularCauchyExtensionalityUp,
      regularCauchyExtensionalityFields x =
          regularCauchyExtensionalityFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R0a R1a S0a S1a Da Ta A0a A1a Ha Ca Pa Na =>
      cases y with
      | mk R0b R1b S0b S1b Db Tb A0b A1b Hb Cb Pb Nb =>
          cases hfields
          rfl

instance regularCauchyExtensionalityBHistCarrier :
    BHistCarrier RegularCauchyExtensionalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyExtensionalityToEventFlow
  fromEventFlow := regularCauchyExtensionalityFromEventFlow

instance regularCauchyExtensionalityChapterTasteGate :
    ChapterTasteGate RegularCauchyExtensionalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyExtensionalityFromEventFlow
          (regularCauchyExtensionalityToEventFlow x) =
        some x
    exact regularCauchyExtensionality_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyExtensionalityToEventFlow_injective heq)

instance regularCauchyExtensionalityFieldFaithful :
    FieldFaithful RegularCauchyExtensionalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyExtensionalityFields
  field_faithful := regularCauchyExtensionality_fields_faithful

instance regularCauchyExtensionalityNontrivial :
    Nontrivial RegularCauchyExtensionalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyExtensionalityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyExtensionalityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyExtensionalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyExtensionalityChapterTasteGate

theorem RegularCauchyExtensionalityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyExtensionalityDecodeBHist
          (regularCauchyExtensionalityEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyExtensionalityUp,
        regularCauchyExtensionalityToEventFlow x =
          List.map regularCauchyExtensionalityEncodeBHist
            (regularCauchyExtensionalityFields x)) ∧
        (∀ x y : RegularCauchyExtensionalityUp,
          regularCauchyExtensionalityFields x =
              regularCauchyExtensionalityFields y →
            x = y) ∧
          (∃ x y : RegularCauchyExtensionalityUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact regularCauchyExtensionality_decode_encode
  · constructor
    · intro x
      rfl
    · constructor
      · exact regularCauchyExtensionality_fields_faithful
      · exact
          ⟨RegularCauchyExtensionalityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty,
            RegularCauchyExtensionalityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty,
            by
              intro h
              cases h⟩

end BEDC.Derived.RegularCauchyExtensionalityUp.TasteGate
