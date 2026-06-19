import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyEvenOddSubstreamsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyEvenOddSubstreamsUp : Type where
  | mk (S E O D R A B H C P N : BHist) : RegularCauchyEvenOddSubstreamsUp
  deriving DecidableEq

def regularCauchyEvenOddSubstreamsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyEvenOddSubstreamsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyEvenOddSubstreamsEncodeBHist h

def regularCauchyEvenOddSubstreamsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyEvenOddSubstreamsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyEvenOddSubstreamsDecodeBHist tail)

private theorem regularCauchyEvenOddSubstreamsDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyEvenOddSubstreamsFields :
    RegularCauchyEvenOddSubstreamsUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyEvenOddSubstreamsUp.mk S E O D R A B H C P N =>
      [S, E, O, D, R, A, B, H, C, P, N]

def regularCauchyEvenOddSubstreamsToEventFlow :
    RegularCauchyEvenOddSubstreamsUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyEvenOddSubstreamsFields x).map
        regularCauchyEvenOddSubstreamsEncodeBHist

private def regularCauchyEvenOddSubstreamsEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyEvenOddSubstreamsEventAtDefault index rest

def regularCauchyEvenOddSubstreamsFromEventFlow
    (ef : EventFlow) : Option RegularCauchyEvenOddSubstreamsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyEvenOddSubstreamsUp.mk
      (regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEventAtDefault 0 ef))
      (regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEventAtDefault 1 ef))
      (regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEventAtDefault 2 ef))
      (regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEventAtDefault 3 ef))
      (regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEventAtDefault 4 ef))
      (regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEventAtDefault 5 ef))
      (regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEventAtDefault 6 ef))
      (regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEventAtDefault 7 ef))
      (regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEventAtDefault 8 ef))
      (regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEventAtDefault 9 ef))
      (regularCauchyEvenOddSubstreamsDecodeBHist
        (regularCauchyEvenOddSubstreamsEventAtDefault 10 ef)))

private theorem RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyEvenOddSubstreamsUp) :
    regularCauchyEvenOddSubstreamsFromEventFlow
      (regularCauchyEvenOddSubstreamsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S E O D R A B H C P N =>
      change
        some
          (RegularCauchyEvenOddSubstreamsUp.mk
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist S))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist E))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist O))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist D))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist R))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist A))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist B))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist H))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist C))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist P))
            (regularCauchyEvenOddSubstreamsDecodeBHist
              (regularCauchyEvenOddSubstreamsEncodeBHist N))) =
          some (RegularCauchyEvenOddSubstreamsUp.mk S E O D R A B H C P N)
      rw [regularCauchyEvenOddSubstreamsDecode_encode_bhist S,
        regularCauchyEvenOddSubstreamsDecode_encode_bhist E,
        regularCauchyEvenOddSubstreamsDecode_encode_bhist O,
        regularCauchyEvenOddSubstreamsDecode_encode_bhist D,
        regularCauchyEvenOddSubstreamsDecode_encode_bhist R,
        regularCauchyEvenOddSubstreamsDecode_encode_bhist A,
        regularCauchyEvenOddSubstreamsDecode_encode_bhist B,
        regularCauchyEvenOddSubstreamsDecode_encode_bhist H,
        regularCauchyEvenOddSubstreamsDecode_encode_bhist C,
        regularCauchyEvenOddSubstreamsDecode_encode_bhist P,
        regularCauchyEvenOddSubstreamsDecode_encode_bhist N]

private theorem regularCauchyEvenOddSubstreamsToEventFlow_injective
    {x y : RegularCauchyEvenOddSubstreamsUp} :
    regularCauchyEvenOddSubstreamsToEventFlow x =
        regularCauchyEvenOddSubstreamsToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyEvenOddSubstreamsFromEventFlow
          (regularCauchyEvenOddSubstreamsToEventFlow x) =
        regularCauchyEvenOddSubstreamsFromEventFlow
          (regularCauchyEvenOddSubstreamsToEventFlow y) :=
    congrArg regularCauchyEvenOddSubstreamsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyEvenOddSubstreamsBHistCarrier :
    BHistCarrier RegularCauchyEvenOddSubstreamsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyEvenOddSubstreamsToEventFlow
  fromEventFlow := regularCauchyEvenOddSubstreamsFromEventFlow

instance regularCauchyEvenOddSubstreamsChapterTasteGate :
    ChapterTasteGate RegularCauchyEvenOddSubstreamsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyEvenOddSubstreamsFromEventFlow
        (regularCauchyEvenOddSubstreamsToEventFlow x) = some x
    exact RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyEvenOddSubstreamsToEventFlow_injective heq)

theorem RegularCauchyEvenOddSubstreamsTasteGate_single_carrier_alignment :
    ChapterTasteGate RegularCauchyEvenOddSubstreamsUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact regularCauchyEvenOddSubstreamsChapterTasteGate

end BEDC.Derived.RegularCauchyEvenOddSubstreamsUp
