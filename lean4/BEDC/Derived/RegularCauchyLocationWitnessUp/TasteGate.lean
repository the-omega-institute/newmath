import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocationWitnessUp

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

private theorem regularCauchyLocationWitnessDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyLocationWitnessDecodeBHist
          (regularCauchyLocationWitnessEncodeBHist h) =
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

def regularCauchyLocationWitnessFields :
    RegularCauchyLocationWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLocationWitnessUp.mk R S D W E H C P N => [R, S, D, W, E, H, C, P, N]

def regularCauchyLocationWitnessToEventFlow :
    RegularCauchyLocationWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyLocationWitnessFields x).map regularCauchyLocationWitnessEncodeBHist

private def regularCauchyLocationWitnessRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => regularCauchyLocationWitnessRawAt n rest

private def regularCauchyLocationWitnessLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => regularCauchyLocationWitnessLengthEq n rest

def regularCauchyLocationWitnessFromEventFlow :
    EventFlow → Option RegularCauchyLocationWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchyLocationWitnessLengthEq 9 flow with
      | true =>
          some
            (RegularCauchyLocationWitnessUp.mk
              (regularCauchyLocationWitnessDecodeBHist
                (regularCauchyLocationWitnessRawAt 0 flow))
              (regularCauchyLocationWitnessDecodeBHist
                (regularCauchyLocationWitnessRawAt 1 flow))
              (regularCauchyLocationWitnessDecodeBHist
                (regularCauchyLocationWitnessRawAt 2 flow))
              (regularCauchyLocationWitnessDecodeBHist
                (regularCauchyLocationWitnessRawAt 3 flow))
              (regularCauchyLocationWitnessDecodeBHist
                (regularCauchyLocationWitnessRawAt 4 flow))
              (regularCauchyLocationWitnessDecodeBHist
                (regularCauchyLocationWitnessRawAt 5 flow))
              (regularCauchyLocationWitnessDecodeBHist
                (regularCauchyLocationWitnessRawAt 6 flow))
              (regularCauchyLocationWitnessDecodeBHist
                (regularCauchyLocationWitnessRawAt 7 flow))
              (regularCauchyLocationWitnessDecodeBHist
                (regularCauchyLocationWitnessRawAt 8 flow)))
      | false => none

private theorem regularCauchyLocationWitness_round_trip :
    ∀ x : RegularCauchyLocationWitnessUp,
      regularCauchyLocationWitnessFromEventFlow
          (regularCauchyLocationWitnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
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
      rw [regularCauchyLocationWitnessDecode_encode_bhist R,
        regularCauchyLocationWitnessDecode_encode_bhist S,
        regularCauchyLocationWitnessDecode_encode_bhist D,
        regularCauchyLocationWitnessDecode_encode_bhist W,
        regularCauchyLocationWitnessDecode_encode_bhist E,
        regularCauchyLocationWitnessDecode_encode_bhist H,
        regularCauchyLocationWitnessDecode_encode_bhist C,
        regularCauchyLocationWitnessDecode_encode_bhist P,
        regularCauchyLocationWitnessDecode_encode_bhist N]

private theorem regularCauchyLocationWitnessToEventFlow_injective
    {x y : RegularCauchyLocationWitnessUp} :
    regularCauchyLocationWitnessToEventFlow x =
        regularCauchyLocationWitnessToEventFlow y →
      x = y := by
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
    change
      regularCauchyLocationWitnessFromEventFlow
          (regularCauchyLocationWitnessToEventFlow x) =
        some x
    exact regularCauchyLocationWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLocationWitnessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyLocationWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyLocationWitnessChapterTasteGate

theorem RegularCauchyLocationWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyLocationWitnessDecodeBHist
        (regularCauchyLocationWitnessEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyLocationWitnessUp,
        regularCauchyLocationWitnessFromEventFlow
          (regularCauchyLocationWitnessToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyLocationWitnessUp,
          regularCauchyLocationWitnessToEventFlow x =
            regularCauchyLocationWitnessToEventFlow y → x = y) ∧
          regularCauchyLocationWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyLocationWitnessDecode_encode_bhist
  · constructor
    · exact regularCauchyLocationWitness_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyLocationWitnessToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyLocationWitnessUp
