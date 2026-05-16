import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyRegularityWitnessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyRegularityWitnessUp : Type where
  | mk (S mu j Omega R Q E H C P N : BHist) : RegularCauchyRegularityWitnessUp
  deriving DecidableEq

def regularCauchyRegularityWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyRegularityWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyRegularityWitnessEncodeBHist h

def regularCauchyRegularityWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyRegularityWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyRegularityWitnessDecodeBHist tail)

private theorem regularCauchyRegularityWitness_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyRegularityWitnessDecodeBHist
        (regularCauchyRegularityWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyRegularityWitnessToEventFlow :
    RegularCauchyRegularityWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyRegularityWitnessUp.mk S mu j Omega R Q E H C P N =>
      [regularCauchyRegularityWitnessEncodeBHist S,
        regularCauchyRegularityWitnessEncodeBHist mu,
        regularCauchyRegularityWitnessEncodeBHist j,
        regularCauchyRegularityWitnessEncodeBHist Omega,
        regularCauchyRegularityWitnessEncodeBHist R,
        regularCauchyRegularityWitnessEncodeBHist Q,
        regularCauchyRegularityWitnessEncodeBHist E,
        regularCauchyRegularityWitnessEncodeBHist H,
        regularCauchyRegularityWitnessEncodeBHist C,
        regularCauchyRegularityWitnessEncodeBHist P,
        regularCauchyRegularityWitnessEncodeBHist N]

private def regularCauchyRegularityWitnessEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyRegularityWitnessEventAtDefault index rest

def regularCauchyRegularityWitnessFromEventFlow (ef : EventFlow) :
    Option RegularCauchyRegularityWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyRegularityWitnessUp.mk
      (regularCauchyRegularityWitnessDecodeBHist
        (regularCauchyRegularityWitnessEventAtDefault 0 ef))
      (regularCauchyRegularityWitnessDecodeBHist
        (regularCauchyRegularityWitnessEventAtDefault 1 ef))
      (regularCauchyRegularityWitnessDecodeBHist
        (regularCauchyRegularityWitnessEventAtDefault 2 ef))
      (regularCauchyRegularityWitnessDecodeBHist
        (regularCauchyRegularityWitnessEventAtDefault 3 ef))
      (regularCauchyRegularityWitnessDecodeBHist
        (regularCauchyRegularityWitnessEventAtDefault 4 ef))
      (regularCauchyRegularityWitnessDecodeBHist
        (regularCauchyRegularityWitnessEventAtDefault 5 ef))
      (regularCauchyRegularityWitnessDecodeBHist
        (regularCauchyRegularityWitnessEventAtDefault 6 ef))
      (regularCauchyRegularityWitnessDecodeBHist
        (regularCauchyRegularityWitnessEventAtDefault 7 ef))
      (regularCauchyRegularityWitnessDecodeBHist
        (regularCauchyRegularityWitnessEventAtDefault 8 ef))
      (regularCauchyRegularityWitnessDecodeBHist
        (regularCauchyRegularityWitnessEventAtDefault 9 ef))
      (regularCauchyRegularityWitnessDecodeBHist
        (regularCauchyRegularityWitnessEventAtDefault 10 ef)))

private theorem regularCauchyRegularityWitness_round_trip :
    ∀ x : RegularCauchyRegularityWitnessUp,
      regularCauchyRegularityWitnessFromEventFlow
        (regularCauchyRegularityWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S mu j Omega R Q E H C P N =>
      change
        some
          (RegularCauchyRegularityWitnessUp.mk
            (regularCauchyRegularityWitnessDecodeBHist
              (regularCauchyRegularityWitnessEncodeBHist S))
            (regularCauchyRegularityWitnessDecodeBHist
              (regularCauchyRegularityWitnessEncodeBHist mu))
            (regularCauchyRegularityWitnessDecodeBHist
              (regularCauchyRegularityWitnessEncodeBHist j))
            (regularCauchyRegularityWitnessDecodeBHist
              (regularCauchyRegularityWitnessEncodeBHist Omega))
            (regularCauchyRegularityWitnessDecodeBHist
              (regularCauchyRegularityWitnessEncodeBHist R))
            (regularCauchyRegularityWitnessDecodeBHist
              (regularCauchyRegularityWitnessEncodeBHist Q))
            (regularCauchyRegularityWitnessDecodeBHist
              (regularCauchyRegularityWitnessEncodeBHist E))
            (regularCauchyRegularityWitnessDecodeBHist
              (regularCauchyRegularityWitnessEncodeBHist H))
            (regularCauchyRegularityWitnessDecodeBHist
              (regularCauchyRegularityWitnessEncodeBHist C))
            (regularCauchyRegularityWitnessDecodeBHist
              (regularCauchyRegularityWitnessEncodeBHist P))
            (regularCauchyRegularityWitnessDecodeBHist
              (regularCauchyRegularityWitnessEncodeBHist N))) =
          some (RegularCauchyRegularityWitnessUp.mk S mu j Omega R Q E H C P N)
      rw [regularCauchyRegularityWitness_decode_encode_bhist S,
        regularCauchyRegularityWitness_decode_encode_bhist mu,
        regularCauchyRegularityWitness_decode_encode_bhist j,
        regularCauchyRegularityWitness_decode_encode_bhist Omega,
        regularCauchyRegularityWitness_decode_encode_bhist R,
        regularCauchyRegularityWitness_decode_encode_bhist Q,
        regularCauchyRegularityWitness_decode_encode_bhist E,
        regularCauchyRegularityWitness_decode_encode_bhist H,
        regularCauchyRegularityWitness_decode_encode_bhist C,
        regularCauchyRegularityWitness_decode_encode_bhist P,
        regularCauchyRegularityWitness_decode_encode_bhist N]

private theorem regularCauchyRegularityWitnessToEventFlow_injective
    {x y : RegularCauchyRegularityWitnessUp} :
    regularCauchyRegularityWitnessToEventFlow x =
      regularCauchyRegularityWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyRegularityWitnessFromEventFlow
          (regularCauchyRegularityWitnessToEventFlow x) =
        regularCauchyRegularityWitnessFromEventFlow
          (regularCauchyRegularityWitnessToEventFlow y) :=
    congrArg regularCauchyRegularityWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyRegularityWitness_round_trip x).symm
      (Eq.trans hread (regularCauchyRegularityWitness_round_trip y)))

private def regularCauchyRegularityWitnessFields :
    RegularCauchyRegularityWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyRegularityWitnessUp.mk S mu j Omega R Q E H C P N =>
      [S, mu, j, Omega, R, Q, E, H, C, P, N]

private theorem regularCauchyRegularityWitness_field_faithful :
    ∀ x y : RegularCauchyRegularityWitnessUp,
      regularCauchyRegularityWitnessFields x = regularCauchyRegularityWitnessFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ mu₁ j₁ Omega₁ R₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ mu₂ j₂ Omega₂ R₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyRegularityWitnessBHistCarrier :
    BHistCarrier RegularCauchyRegularityWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyRegularityWitnessToEventFlow
  fromEventFlow := regularCauchyRegularityWitnessFromEventFlow

instance regularCauchyRegularityWitnessChapterTasteGate :
    ChapterTasteGate RegularCauchyRegularityWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyRegularityWitnessFromEventFlow
      (regularCauchyRegularityWitnessToEventFlow x) = some x
    exact regularCauchyRegularityWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyRegularityWitnessToEventFlow_injective heq)

instance regularCauchyRegularityWitnessFieldFaithful :
    FieldFaithful RegularCauchyRegularityWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyRegularityWitnessFields
  field_faithful := regularCauchyRegularityWitness_field_faithful

instance regularCauchyRegularityWitnessNontrivial :
    Nontrivial RegularCauchyRegularityWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyRegularityWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyRegularityWitnessUp.mk (BHist.e1 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyRegularityWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyRegularityWitnessChapterTasteGate

theorem RegularCauchyRegularityWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyRegularityWitnessDecodeBHist
          (regularCauchyRegularityWitnessEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyRegularityWitnessUp,
        regularCauchyRegularityWitnessFromEventFlow
          (regularCauchyRegularityWitnessToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyRegularityWitnessUp,
          regularCauchyRegularityWitnessToEventFlow x =
            regularCauchyRegularityWitnessToEventFlow y → x = y) ∧
          regularCauchyRegularityWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk S mu j Omega R Q E H C P N =>
          change
            some
              (RegularCauchyRegularityWitnessUp.mk
                (regularCauchyRegularityWitnessDecodeBHist
                  (regularCauchyRegularityWitnessEncodeBHist S))
                (regularCauchyRegularityWitnessDecodeBHist
                  (regularCauchyRegularityWitnessEncodeBHist mu))
                (regularCauchyRegularityWitnessDecodeBHist
                  (regularCauchyRegularityWitnessEncodeBHist j))
                (regularCauchyRegularityWitnessDecodeBHist
                  (regularCauchyRegularityWitnessEncodeBHist Omega))
                (regularCauchyRegularityWitnessDecodeBHist
                  (regularCauchyRegularityWitnessEncodeBHist R))
                (regularCauchyRegularityWitnessDecodeBHist
                  (regularCauchyRegularityWitnessEncodeBHist Q))
                (regularCauchyRegularityWitnessDecodeBHist
                  (regularCauchyRegularityWitnessEncodeBHist E))
                (regularCauchyRegularityWitnessDecodeBHist
                  (regularCauchyRegularityWitnessEncodeBHist H))
                (regularCauchyRegularityWitnessDecodeBHist
                  (regularCauchyRegularityWitnessEncodeBHist C))
                (regularCauchyRegularityWitnessDecodeBHist
                  (regularCauchyRegularityWitnessEncodeBHist P))
                (regularCauchyRegularityWitnessDecodeBHist
                  (regularCauchyRegularityWitnessEncodeBHist N))) =
              some (RegularCauchyRegularityWitnessUp.mk S mu j Omega R Q E H C P N)
          rw [regularCauchyRegularityWitness_decode_encode_bhist S,
            regularCauchyRegularityWitness_decode_encode_bhist mu,
            regularCauchyRegularityWitness_decode_encode_bhist j,
            regularCauchyRegularityWitness_decode_encode_bhist Omega,
            regularCauchyRegularityWitness_decode_encode_bhist R,
            regularCauchyRegularityWitness_decode_encode_bhist Q,
            regularCauchyRegularityWitness_decode_encode_bhist E,
            regularCauchyRegularityWitness_decode_encode_bhist H,
            regularCauchyRegularityWitness_decode_encode_bhist C,
            regularCauchyRegularityWitness_decode_encode_bhist P,
            regularCauchyRegularityWitness_decode_encode_bhist N]
    · constructor
      · intro x y heq
        have hread :
            regularCauchyRegularityWitnessFromEventFlow
                (regularCauchyRegularityWitnessToEventFlow x) =
              regularCauchyRegularityWitnessFromEventFlow
                (regularCauchyRegularityWitnessToEventFlow y) :=
          congrArg regularCauchyRegularityWitnessFromEventFlow heq
        exact Option.some.inj
          (Eq.trans (regularCauchyRegularityWitness_round_trip x).symm
            (Eq.trans hread (regularCauchyRegularityWitness_round_trip y)))
      · rfl

end BEDC.Derived.RegularCauchyRegularityWitnessUp.TasteGate
