import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MintyBrowderMonotoneOperatorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MintyBrowderMonotoneOperatorUp : Type where
  | mk (X A G R W D H C P N : BHist) : MintyBrowderMonotoneOperatorUp
  deriving DecidableEq

def mintyBrowderMonotoneOperatorEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mintyBrowderMonotoneOperatorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mintyBrowderMonotoneOperatorEncodeBHist h

def mintyBrowderMonotoneOperatorDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mintyBrowderMonotoneOperatorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mintyBrowderMonotoneOperatorDecodeBHist tail)

private theorem MintyBrowderMonotoneOperatorTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      mintyBrowderMonotoneOperatorDecodeBHist
        (mintyBrowderMonotoneOperatorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def mintyBrowderMonotoneOperatorFields :
    MintyBrowderMonotoneOperatorUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MintyBrowderMonotoneOperatorUp.mk X A G R W D H C P N => [X, A, G, R, W, D, H, C, P, N]

def mintyBrowderMonotoneOperatorToEventFlow :
    MintyBrowderMonotoneOperatorUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (mintyBrowderMonotoneOperatorFields x).map mintyBrowderMonotoneOperatorEncodeBHist

private def mintyBrowderMonotoneOperatorRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => mintyBrowderMonotoneOperatorRawAt n rest

private def mintyBrowderMonotoneOperatorLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => mintyBrowderMonotoneOperatorLengthEq n rest

def mintyBrowderMonotoneOperatorFromEventFlow
    (flow : EventFlow) : Option MintyBrowderMonotoneOperatorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match mintyBrowderMonotoneOperatorLengthEq 10 flow with
  | true =>
      some
        (MintyBrowderMonotoneOperatorUp.mk
          (mintyBrowderMonotoneOperatorDecodeBHist
            (mintyBrowderMonotoneOperatorRawAt 0 flow))
          (mintyBrowderMonotoneOperatorDecodeBHist
            (mintyBrowderMonotoneOperatorRawAt 1 flow))
          (mintyBrowderMonotoneOperatorDecodeBHist
            (mintyBrowderMonotoneOperatorRawAt 2 flow))
          (mintyBrowderMonotoneOperatorDecodeBHist
            (mintyBrowderMonotoneOperatorRawAt 3 flow))
          (mintyBrowderMonotoneOperatorDecodeBHist
            (mintyBrowderMonotoneOperatorRawAt 4 flow))
          (mintyBrowderMonotoneOperatorDecodeBHist
            (mintyBrowderMonotoneOperatorRawAt 5 flow))
          (mintyBrowderMonotoneOperatorDecodeBHist
            (mintyBrowderMonotoneOperatorRawAt 6 flow))
          (mintyBrowderMonotoneOperatorDecodeBHist
            (mintyBrowderMonotoneOperatorRawAt 7 flow))
          (mintyBrowderMonotoneOperatorDecodeBHist
            (mintyBrowderMonotoneOperatorRawAt 8 flow))
          (mintyBrowderMonotoneOperatorDecodeBHist
            (mintyBrowderMonotoneOperatorRawAt 9 flow)))
  | false => none

private theorem mintyBrowderMonotoneOperator_round_trip :
    forall x : MintyBrowderMonotoneOperatorUp,
      mintyBrowderMonotoneOperatorFromEventFlow
        (mintyBrowderMonotoneOperatorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X A G R W D H C P N =>
      change
        some
          (MintyBrowderMonotoneOperatorUp.mk
            (mintyBrowderMonotoneOperatorDecodeBHist
              (mintyBrowderMonotoneOperatorEncodeBHist X))
            (mintyBrowderMonotoneOperatorDecodeBHist
              (mintyBrowderMonotoneOperatorEncodeBHist A))
            (mintyBrowderMonotoneOperatorDecodeBHist
              (mintyBrowderMonotoneOperatorEncodeBHist G))
            (mintyBrowderMonotoneOperatorDecodeBHist
              (mintyBrowderMonotoneOperatorEncodeBHist R))
            (mintyBrowderMonotoneOperatorDecodeBHist
              (mintyBrowderMonotoneOperatorEncodeBHist W))
            (mintyBrowderMonotoneOperatorDecodeBHist
              (mintyBrowderMonotoneOperatorEncodeBHist D))
            (mintyBrowderMonotoneOperatorDecodeBHist
              (mintyBrowderMonotoneOperatorEncodeBHist H))
            (mintyBrowderMonotoneOperatorDecodeBHist
              (mintyBrowderMonotoneOperatorEncodeBHist C))
            (mintyBrowderMonotoneOperatorDecodeBHist
              (mintyBrowderMonotoneOperatorEncodeBHist P))
            (mintyBrowderMonotoneOperatorDecodeBHist
              (mintyBrowderMonotoneOperatorEncodeBHist N))) =
          some (MintyBrowderMonotoneOperatorUp.mk X A G R W D H C P N)
      rw [MintyBrowderMonotoneOperatorTasteGate_single_carrier_alignment_decode X,
        MintyBrowderMonotoneOperatorTasteGate_single_carrier_alignment_decode A,
        MintyBrowderMonotoneOperatorTasteGate_single_carrier_alignment_decode G,
        MintyBrowderMonotoneOperatorTasteGate_single_carrier_alignment_decode R,
        MintyBrowderMonotoneOperatorTasteGate_single_carrier_alignment_decode W,
        MintyBrowderMonotoneOperatorTasteGate_single_carrier_alignment_decode D,
        MintyBrowderMonotoneOperatorTasteGate_single_carrier_alignment_decode H,
        MintyBrowderMonotoneOperatorTasteGate_single_carrier_alignment_decode C,
        MintyBrowderMonotoneOperatorTasteGate_single_carrier_alignment_decode P,
        MintyBrowderMonotoneOperatorTasteGate_single_carrier_alignment_decode N]

private theorem mintyBrowderMonotoneOperatorToEventFlow_injective
    {x y : MintyBrowderMonotoneOperatorUp} :
    mintyBrowderMonotoneOperatorToEventFlow x =
        mintyBrowderMonotoneOperatorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mintyBrowderMonotoneOperatorFromEventFlow
          (mintyBrowderMonotoneOperatorToEventFlow x) =
        mintyBrowderMonotoneOperatorFromEventFlow
          (mintyBrowderMonotoneOperatorToEventFlow y) :=
    congrArg mintyBrowderMonotoneOperatorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (mintyBrowderMonotoneOperator_round_trip x).symm
      (Eq.trans hread (mintyBrowderMonotoneOperator_round_trip y)))

instance mintyBrowderMonotoneOperatorBHistCarrier :
    BHistCarrier MintyBrowderMonotoneOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mintyBrowderMonotoneOperatorToEventFlow
  fromEventFlow := mintyBrowderMonotoneOperatorFromEventFlow

instance mintyBrowderMonotoneOperatorChapterTasteGate :
    ChapterTasteGate MintyBrowderMonotoneOperatorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      mintyBrowderMonotoneOperatorFromEventFlow
        (mintyBrowderMonotoneOperatorToEventFlow x) = some x
    exact mintyBrowderMonotoneOperator_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (mintyBrowderMonotoneOperatorToEventFlow_injective heq)

theorem MintyBrowderMonotoneOperatorTasteGate_single_carrier_alignment :
    (forall h : BHist, mintyBrowderMonotoneOperatorDecodeBHist
      (mintyBrowderMonotoneOperatorEncodeBHist h) = h) ∧
    (forall x : MintyBrowderMonotoneOperatorUp,
      mintyBrowderMonotoneOperatorFromEventFlow
        (mintyBrowderMonotoneOperatorToEventFlow x) = some x) ∧
    (forall x y : MintyBrowderMonotoneOperatorUp,
      mintyBrowderMonotoneOperatorToEventFlow x =
        mintyBrowderMonotoneOperatorToEventFlow y -> x = y) ∧
    mintyBrowderMonotoneOperatorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MintyBrowderMonotoneOperatorTasteGate_single_carrier_alignment_decode
  · constructor
    · exact mintyBrowderMonotoneOperator_round_trip
    · constructor
      · intro x y heq
        exact mintyBrowderMonotoneOperatorToEventFlow_injective heq
      · rfl

end BEDC.Derived.MintyBrowderMonotoneOperatorUp
