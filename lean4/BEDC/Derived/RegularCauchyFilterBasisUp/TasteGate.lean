import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFilterBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFilterBasisUp : Type where
  | mk (S R D B M E H C P N : BHist) : RegularCauchyFilterBasisUp
  deriving DecidableEq

def regularCauchyFilterBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFilterBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFilterBasisEncodeBHist h

def regularCauchyFilterBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFilterBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFilterBasisDecodeBHist tail)

private theorem regularCauchyFilterBasis_decode_encode :
    ∀ h : BHist, regularCauchyFilterBasisDecodeBHist
      (regularCauchyFilterBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyFilterBasisFields : RegularCauchyFilterBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFilterBasisUp.mk S R D B M E H C P N => [S, R, D, B, M, E, H, C, P, N]

def regularCauchyFilterBasisToEventFlow : RegularCauchyFilterBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyFilterBasisFields x).map regularCauchyFilterBasisEncodeBHist

private def regularCauchyFilterBasisRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyFilterBasisRawAt index rest

private def regularCauchyFilterBasisLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _event :: rest => regularCauchyFilterBasisLengthEq index rest

def regularCauchyFilterBasisFromEventFlow :
    EventFlow → Option RegularCauchyFilterBasisUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchyFilterBasisLengthEq 10 flow with
      | true =>
          some
            (RegularCauchyFilterBasisUp.mk
              (regularCauchyFilterBasisDecodeBHist (regularCauchyFilterBasisRawAt 0 flow))
              (regularCauchyFilterBasisDecodeBHist (regularCauchyFilterBasisRawAt 1 flow))
              (regularCauchyFilterBasisDecodeBHist (regularCauchyFilterBasisRawAt 2 flow))
              (regularCauchyFilterBasisDecodeBHist (regularCauchyFilterBasisRawAt 3 flow))
              (regularCauchyFilterBasisDecodeBHist (regularCauchyFilterBasisRawAt 4 flow))
              (regularCauchyFilterBasisDecodeBHist (regularCauchyFilterBasisRawAt 5 flow))
              (regularCauchyFilterBasisDecodeBHist (regularCauchyFilterBasisRawAt 6 flow))
              (regularCauchyFilterBasisDecodeBHist (regularCauchyFilterBasisRawAt 7 flow))
              (regularCauchyFilterBasisDecodeBHist (regularCauchyFilterBasisRawAt 8 flow))
              (regularCauchyFilterBasisDecodeBHist (regularCauchyFilterBasisRawAt 9 flow)))
      | false => none

private theorem regularCauchyFilterBasis_round_trip :
    ∀ x : RegularCauchyFilterBasisUp,
      regularCauchyFilterBasisFromEventFlow
        (regularCauchyFilterBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D B M E H C P N =>
      change
        some
          (RegularCauchyFilterBasisUp.mk
            (regularCauchyFilterBasisDecodeBHist
              (regularCauchyFilterBasisEncodeBHist S))
            (regularCauchyFilterBasisDecodeBHist
              (regularCauchyFilterBasisEncodeBHist R))
            (regularCauchyFilterBasisDecodeBHist
              (regularCauchyFilterBasisEncodeBHist D))
            (regularCauchyFilterBasisDecodeBHist
              (regularCauchyFilterBasisEncodeBHist B))
            (regularCauchyFilterBasisDecodeBHist
              (regularCauchyFilterBasisEncodeBHist M))
            (regularCauchyFilterBasisDecodeBHist
              (regularCauchyFilterBasisEncodeBHist E))
            (regularCauchyFilterBasisDecodeBHist
              (regularCauchyFilterBasisEncodeBHist H))
            (regularCauchyFilterBasisDecodeBHist
              (regularCauchyFilterBasisEncodeBHist C))
            (regularCauchyFilterBasisDecodeBHist
              (regularCauchyFilterBasisEncodeBHist P))
            (regularCauchyFilterBasisDecodeBHist
              (regularCauchyFilterBasisEncodeBHist N))) =
          some (RegularCauchyFilterBasisUp.mk S R D B M E H C P N)
      rw [regularCauchyFilterBasis_decode_encode S,
        regularCauchyFilterBasis_decode_encode R,
        regularCauchyFilterBasis_decode_encode D,
        regularCauchyFilterBasis_decode_encode B,
        regularCauchyFilterBasis_decode_encode M,
        regularCauchyFilterBasis_decode_encode E,
        regularCauchyFilterBasis_decode_encode H,
        regularCauchyFilterBasis_decode_encode C,
        regularCauchyFilterBasis_decode_encode P,
        regularCauchyFilterBasis_decode_encode N]

private theorem regularCauchyFilterBasisToEventFlow_injective
    {x y : RegularCauchyFilterBasisUp} :
    regularCauchyFilterBasisToEventFlow x =
      regularCauchyFilterBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFilterBasisFromEventFlow (regularCauchyFilterBasisToEventFlow x) =
        regularCauchyFilterBasisFromEventFlow (regularCauchyFilterBasisToEventFlow y) :=
    congrArg regularCauchyFilterBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyFilterBasis_round_trip x).symm
      (Eq.trans hread (regularCauchyFilterBasis_round_trip y)))

instance regularCauchyFilterBasisBHistCarrier :
    BHistCarrier RegularCauchyFilterBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFilterBasisToEventFlow
  fromEventFlow := regularCauchyFilterBasisFromEventFlow

instance regularCauchyFilterBasisChapterTasteGate :
    ChapterTasteGate RegularCauchyFilterBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyFilterBasisFromEventFlow
        (regularCauchyFilterBasisToEventFlow x) = some x
    exact regularCauchyFilterBasis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyFilterBasisToEventFlow_injective heq)

theorem RegularCauchyFilterBasisTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyFilterBasisDecodeBHist
      (regularCauchyFilterBasisEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyFilterBasisUp,
        regularCauchyFilterBasisFromEventFlow
          (regularCauchyFilterBasisToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyFilterBasisUp,
          regularCauchyFilterBasisToEventFlow x =
            regularCauchyFilterBasisToEventFlow y → x = y) ∧
          regularCauchyFilterBasisEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyFilterBasis_decode_encode
  · constructor
    · exact regularCauchyFilterBasis_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyFilterBasisToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyFilterBasisUp
