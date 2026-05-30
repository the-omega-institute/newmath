import BEDC.Derived.CauchyOscillationCriterionUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyOscillationCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchyOscillationCriterionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyOscillationCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyOscillationCriterionEncodeBHist h

def cauchyOscillationCriterionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyOscillationCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyOscillationCriterionDecodeBHist tail)

private theorem cauchyOscillationCriterion_decode_encode_bhist :
    forall h : BHist,
      cauchyOscillationCriterionDecodeBHist
        (cauchyOscillationCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyOscillationCriterionFields :
    CauchyOscillationCriterionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyOscillationCriterionUp.mk O K A U Q R H C P N =>
      [O, K, A, U, Q, R, H, C, P, N]

def cauchyOscillationCriterionToEventFlow :
    CauchyOscillationCriterionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyOscillationCriterionFields x).map
        cauchyOscillationCriterionEncodeBHist

private def cauchyOscillationCriterionEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyOscillationCriterionEventAtDefault index rest

def cauchyOscillationCriterionFromEventFlow
    (flow : EventFlow) : Option CauchyOscillationCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyOscillationCriterionUp.mk
      (cauchyOscillationCriterionDecodeBHist
        (cauchyOscillationCriterionEventAtDefault 0 flow))
      (cauchyOscillationCriterionDecodeBHist
        (cauchyOscillationCriterionEventAtDefault 1 flow))
      (cauchyOscillationCriterionDecodeBHist
        (cauchyOscillationCriterionEventAtDefault 2 flow))
      (cauchyOscillationCriterionDecodeBHist
        (cauchyOscillationCriterionEventAtDefault 3 flow))
      (cauchyOscillationCriterionDecodeBHist
        (cauchyOscillationCriterionEventAtDefault 4 flow))
      (cauchyOscillationCriterionDecodeBHist
        (cauchyOscillationCriterionEventAtDefault 5 flow))
      (cauchyOscillationCriterionDecodeBHist
        (cauchyOscillationCriterionEventAtDefault 6 flow))
      (cauchyOscillationCriterionDecodeBHist
        (cauchyOscillationCriterionEventAtDefault 7 flow))
      (cauchyOscillationCriterionDecodeBHist
        (cauchyOscillationCriterionEventAtDefault 8 flow))
      (cauchyOscillationCriterionDecodeBHist
        (cauchyOscillationCriterionEventAtDefault 9 flow)))

private theorem cauchyOscillationCriterion_round_trip :
    forall x : CauchyOscillationCriterionUp,
      cauchyOscillationCriterionFromEventFlow
        (cauchyOscillationCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O K A U Q R H C P N =>
      change
        some
          (CauchyOscillationCriterionUp.mk
            (cauchyOscillationCriterionDecodeBHist
              (cauchyOscillationCriterionEncodeBHist O))
            (cauchyOscillationCriterionDecodeBHist
              (cauchyOscillationCriterionEncodeBHist K))
            (cauchyOscillationCriterionDecodeBHist
              (cauchyOscillationCriterionEncodeBHist A))
            (cauchyOscillationCriterionDecodeBHist
              (cauchyOscillationCriterionEncodeBHist U))
            (cauchyOscillationCriterionDecodeBHist
              (cauchyOscillationCriterionEncodeBHist Q))
            (cauchyOscillationCriterionDecodeBHist
              (cauchyOscillationCriterionEncodeBHist R))
            (cauchyOscillationCriterionDecodeBHist
              (cauchyOscillationCriterionEncodeBHist H))
            (cauchyOscillationCriterionDecodeBHist
              (cauchyOscillationCriterionEncodeBHist C))
            (cauchyOscillationCriterionDecodeBHist
              (cauchyOscillationCriterionEncodeBHist P))
            (cauchyOscillationCriterionDecodeBHist
              (cauchyOscillationCriterionEncodeBHist N))) =
          some (CauchyOscillationCriterionUp.mk O K A U Q R H C P N)
      rw [cauchyOscillationCriterion_decode_encode_bhist O,
        cauchyOscillationCriterion_decode_encode_bhist K,
        cauchyOscillationCriterion_decode_encode_bhist A,
        cauchyOscillationCriterion_decode_encode_bhist U,
        cauchyOscillationCriterion_decode_encode_bhist Q,
        cauchyOscillationCriterion_decode_encode_bhist R,
        cauchyOscillationCriterion_decode_encode_bhist H,
        cauchyOscillationCriterion_decode_encode_bhist C,
        cauchyOscillationCriterion_decode_encode_bhist P,
        cauchyOscillationCriterion_decode_encode_bhist N]

private theorem CauchyOscillationCriterionToEventFlow_injective
    {x y : CauchyOscillationCriterionUp} :
    cauchyOscillationCriterionToEventFlow x =
      cauchyOscillationCriterionToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyOscillationCriterionFromEventFlow
          (cauchyOscillationCriterionToEventFlow x) =
        cauchyOscillationCriterionFromEventFlow
          (cauchyOscillationCriterionToEventFlow y) :=
    congrArg cauchyOscillationCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyOscillationCriterion_round_trip x).symm
      (Eq.trans hread (cauchyOscillationCriterion_round_trip y)))

instance cauchyOscillationCriterionBHistCarrier :
    BHistCarrier CauchyOscillationCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyOscillationCriterionToEventFlow
  fromEventFlow := cauchyOscillationCriterionFromEventFlow

instance cauchyOscillationCriterionChapterTasteGate :
    ChapterTasteGate CauchyOscillationCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyOscillationCriterionFromEventFlow
        (cauchyOscillationCriterionToEventFlow x) = some x
    exact cauchyOscillationCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyOscillationCriterionToEventFlow_injective heq)

theorem CauchyOscillationCriterionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchyOscillationCriterionDecodeBHist
        (cauchyOscillationCriterionEncodeBHist h) = h) /\
      (forall x : CauchyOscillationCriterionUp,
        cauchyOscillationCriterionFromEventFlow
          (cauchyOscillationCriterionToEventFlow x) = some x) /\
        (forall x y : CauchyOscillationCriterionUp,
          cauchyOscillationCriterionToEventFlow x =
            cauchyOscillationCriterionToEventFlow y -> x = y) /\
          cauchyOscillationCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyOscillationCriterion_decode_encode_bhist,
      cauchyOscillationCriterion_round_trip,
      (fun _ _ heq => CauchyOscillationCriterionToEventFlow_injective heq), rfl⟩

end BEDC.Derived.CauchyOscillationCriterionUp
