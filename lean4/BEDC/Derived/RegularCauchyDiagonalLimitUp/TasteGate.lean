import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDiagonalLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDiagonalLimitUp : Type where
  | mk (S W R Q E H C P N : BHist) : RegularCauchyDiagonalLimitUp
  deriving DecidableEq

def regularCauchyDiagonalLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDiagonalLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDiagonalLimitEncodeBHist h

def regularCauchyDiagonalLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDiagonalLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDiagonalLimitDecodeBHist tail)

private theorem regularCauchyDiagonalLimitDecode_encode :
    ∀ h : BHist,
      regularCauchyDiagonalLimitDecodeBHist
          (regularCauchyDiagonalLimitEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyDiagonalLimitFields :
    RegularCauchyDiagonalLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDiagonalLimitUp.mk S W R Q E H C P N => [S, W, R, Q, E, H, C, P, N]

def regularCauchyDiagonalLimitToEventFlow :
    RegularCauchyDiagonalLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyDiagonalLimitFields x).map regularCauchyDiagonalLimitEncodeBHist

private def regularCauchyDiagonalLimitEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyDiagonalLimitEventAt index rest

def regularCauchyDiagonalLimitFromEventFlow :
    EventFlow → Option RegularCauchyDiagonalLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyDiagonalLimitUp.mk
        (regularCauchyDiagonalLimitDecodeBHist
          (regularCauchyDiagonalLimitEventAt 0 ef))
        (regularCauchyDiagonalLimitDecodeBHist
          (regularCauchyDiagonalLimitEventAt 1 ef))
        (regularCauchyDiagonalLimitDecodeBHist
          (regularCauchyDiagonalLimitEventAt 2 ef))
        (regularCauchyDiagonalLimitDecodeBHist
          (regularCauchyDiagonalLimitEventAt 3 ef))
        (regularCauchyDiagonalLimitDecodeBHist
          (regularCauchyDiagonalLimitEventAt 4 ef))
        (regularCauchyDiagonalLimitDecodeBHist
          (regularCauchyDiagonalLimitEventAt 5 ef))
        (regularCauchyDiagonalLimitDecodeBHist
          (regularCauchyDiagonalLimitEventAt 6 ef))
        (regularCauchyDiagonalLimitDecodeBHist
          (regularCauchyDiagonalLimitEventAt 7 ef))
        (regularCauchyDiagonalLimitDecodeBHist
          (regularCauchyDiagonalLimitEventAt 8 ef)))

private theorem regularCauchyDiagonalLimit_round_trip :
    ∀ x : RegularCauchyDiagonalLimitUp,
      regularCauchyDiagonalLimitFromEventFlow
          (regularCauchyDiagonalLimitToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W R Q E H C P N =>
      change
        some
            (RegularCauchyDiagonalLimitUp.mk
              (regularCauchyDiagonalLimitDecodeBHist
                (regularCauchyDiagonalLimitEncodeBHist S))
              (regularCauchyDiagonalLimitDecodeBHist
                (regularCauchyDiagonalLimitEncodeBHist W))
              (regularCauchyDiagonalLimitDecodeBHist
                (regularCauchyDiagonalLimitEncodeBHist R))
              (regularCauchyDiagonalLimitDecodeBHist
                (regularCauchyDiagonalLimitEncodeBHist Q))
              (regularCauchyDiagonalLimitDecodeBHist
                (regularCauchyDiagonalLimitEncodeBHist E))
              (regularCauchyDiagonalLimitDecodeBHist
                (regularCauchyDiagonalLimitEncodeBHist H))
              (regularCauchyDiagonalLimitDecodeBHist
                (regularCauchyDiagonalLimitEncodeBHist C))
              (regularCauchyDiagonalLimitDecodeBHist
                (regularCauchyDiagonalLimitEncodeBHist P))
              (regularCauchyDiagonalLimitDecodeBHist
                (regularCauchyDiagonalLimitEncodeBHist N))) =
          some (RegularCauchyDiagonalLimitUp.mk S W R Q E H C P N)
      rw [regularCauchyDiagonalLimitDecode_encode S,
        regularCauchyDiagonalLimitDecode_encode W,
        regularCauchyDiagonalLimitDecode_encode R,
        regularCauchyDiagonalLimitDecode_encode Q,
        regularCauchyDiagonalLimitDecode_encode E,
        regularCauchyDiagonalLimitDecode_encode H,
        regularCauchyDiagonalLimitDecode_encode C,
        regularCauchyDiagonalLimitDecode_encode P,
        regularCauchyDiagonalLimitDecode_encode N]

private theorem regularCauchyDiagonalLimitToEventFlow_injective
    {x y : RegularCauchyDiagonalLimitUp} :
    regularCauchyDiagonalLimitToEventFlow x =
        regularCauchyDiagonalLimitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDiagonalLimitFromEventFlow
          (regularCauchyDiagonalLimitToEventFlow x) =
        regularCauchyDiagonalLimitFromEventFlow
          (regularCauchyDiagonalLimitToEventFlow y) :=
    congrArg regularCauchyDiagonalLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyDiagonalLimit_round_trip x).symm
      (Eq.trans hread (regularCauchyDiagonalLimit_round_trip y)))

instance regularCauchyDiagonalLimitBHistCarrier :
    BHistCarrier RegularCauchyDiagonalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDiagonalLimitToEventFlow
  fromEventFlow := regularCauchyDiagonalLimitFromEventFlow

instance regularCauchyDiagonalLimitChapterTasteGate :
    ChapterTasteGate RegularCauchyDiagonalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyDiagonalLimitFromEventFlow
          (regularCauchyDiagonalLimitToEventFlow x) =
        some x
    exact regularCauchyDiagonalLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDiagonalLimitToEventFlow_injective heq)

theorem RegularCauchyDiagonalLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyDiagonalLimitDecodeBHist
          (regularCauchyDiagonalLimitEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyDiagonalLimitUp,
        regularCauchyDiagonalLimitFromEventFlow
            (regularCauchyDiagonalLimitToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyDiagonalLimitUp,
        regularCauchyDiagonalLimitToEventFlow x =
            regularCauchyDiagonalLimitToEventFlow y →
          x = y) ∧
      regularCauchyDiagonalLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyDiagonalLimitDecode_encode
  constructor
  · exact regularCauchyDiagonalLimit_round_trip
  constructor
  · intro x y
    exact regularCauchyDiagonalLimitToEventFlow_injective
  · rfl

end BEDC.Derived.RegularCauchyDiagonalLimitUp
