import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocatedComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLocatedComparisonUp : Type where
  | mk (X0 X1 W R0 R1 D K E0 E1 H C P N : BHist) :
      RegularCauchyLocatedComparisonUp

def regularCauchyLocatedComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLocatedComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLocatedComparisonEncodeBHist h

def regularCauchyLocatedComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLocatedComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLocatedComparisonDecodeBHist tail)

private theorem RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLocatedComparisonFields :
    RegularCauchyLocatedComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLocatedComparisonUp.mk X0 X1 W R0 R1 D K E0 E1 H C P N =>
      [X0, X1, W, R0, R1, D, K, E0, E1, H, C, P, N]

def regularCauchyLocatedComparisonToEventFlow :
    RegularCauchyLocatedComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyLocatedComparisonFields x).map
        regularCauchyLocatedComparisonEncodeBHist

private def regularCauchyLocatedComparisonRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => regularCauchyLocatedComparisonRawAt index rest

def regularCauchyLocatedComparisonFromEventFlow
    (flow : EventFlow) : Option RegularCauchyLocatedComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyLocatedComparisonUp.mk
      (regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonRawAt 0 flow))
      (regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonRawAt 1 flow))
      (regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonRawAt 2 flow))
      (regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonRawAt 3 flow))
      (regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonRawAt 4 flow))
      (regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonRawAt 5 flow))
      (regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonRawAt 6 flow))
      (regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonRawAt 7 flow))
      (regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonRawAt 8 flow))
      (regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonRawAt 9 flow))
      (regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonRawAt 10 flow))
      (regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonRawAt 11 flow))
      (regularCauchyLocatedComparisonDecodeBHist
        (regularCauchyLocatedComparisonRawAt 12 flow)))

private theorem RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyLocatedComparisonUp) :
    regularCauchyLocatedComparisonFromEventFlow
        (regularCauchyLocatedComparisonToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X0 X1 W R0 R1 D K E0 E1 H C P N =>
      change
        some
          (RegularCauchyLocatedComparisonUp.mk
            (regularCauchyLocatedComparisonDecodeBHist
              (regularCauchyLocatedComparisonEncodeBHist X0))
            (regularCauchyLocatedComparisonDecodeBHist
              (regularCauchyLocatedComparisonEncodeBHist X1))
            (regularCauchyLocatedComparisonDecodeBHist
              (regularCauchyLocatedComparisonEncodeBHist W))
            (regularCauchyLocatedComparisonDecodeBHist
              (regularCauchyLocatedComparisonEncodeBHist R0))
            (regularCauchyLocatedComparisonDecodeBHist
              (regularCauchyLocatedComparisonEncodeBHist R1))
            (regularCauchyLocatedComparisonDecodeBHist
              (regularCauchyLocatedComparisonEncodeBHist D))
            (regularCauchyLocatedComparisonDecodeBHist
              (regularCauchyLocatedComparisonEncodeBHist K))
            (regularCauchyLocatedComparisonDecodeBHist
              (regularCauchyLocatedComparisonEncodeBHist E0))
            (regularCauchyLocatedComparisonDecodeBHist
              (regularCauchyLocatedComparisonEncodeBHist E1))
            (regularCauchyLocatedComparisonDecodeBHist
              (regularCauchyLocatedComparisonEncodeBHist H))
            (regularCauchyLocatedComparisonDecodeBHist
              (regularCauchyLocatedComparisonEncodeBHist C))
            (regularCauchyLocatedComparisonDecodeBHist
              (regularCauchyLocatedComparisonEncodeBHist P))
            (regularCauchyLocatedComparisonDecodeBHist
              (regularCauchyLocatedComparisonEncodeBHist N))) =
          some (RegularCauchyLocatedComparisonUp.mk X0 X1 W R0 R1 D K E0 E1 H C P N)
      rw [RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode X0,
        RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode X1,
        RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode R0,
        RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode R1,
        RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode K,
        RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode E0,
        RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode E1,
        RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyLocatedComparisonUp} :
    regularCauchyLocatedComparisonToEventFlow x =
      regularCauchyLocatedComparisonToEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLocatedComparisonFromEventFlow
          (regularCauchyLocatedComparisonToEventFlow x) =
        regularCauchyLocatedComparisonFromEventFlow
          (regularCauchyLocatedComparisonToEventFlow y) :=
    congrArg regularCauchyLocatedComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyLocatedComparisonBHistCarrier :
    BHistCarrier RegularCauchyLocatedComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLocatedComparisonToEventFlow
  fromEventFlow := regularCauchyLocatedComparisonFromEventFlow

instance regularCauchyLocatedComparisonChapterTasteGate :
    ChapterTasteGate RegularCauchyLocatedComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLocatedComparisonFromEventFlow
          (regularCauchyLocatedComparisonToEventFlow x) =
        some x
    exact RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RegularCauchyLocatedComparisonTasteGate_single_carrier_alignment :
    ChapterTasteGate RegularCauchyLocatedComparisonUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact regularCauchyLocatedComparisonChapterTasteGate

end BEDC.Derived.RegularCauchyLocatedComparisonUp
